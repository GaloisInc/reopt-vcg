{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import           Control.Concurrent
import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad (forM_)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.ElfEdit
import           Data.IORef
import           Data.List as List
import           Data.Macaw.CFG
import           Data.Macaw.Memory.ElfLoader
import qualified Data.Macaw.Types as M
import           Data.Macaw.X86
import           Data.Macaw.X86.X86Reg
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as LText
import qualified Data.Yaml as Yaml
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           Text.LLVM hiding (comment, (:>), Value)
import           Text.LLVM.PP
import qualified What4.Protocol.SMTLib2.Parse as SMTP
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import           Reopt.VCG.Config
import           VCGCommon
import qualified VCGLLVM as L
import qualified VCGMacaw as M


-- Maps LLVM block labels to the information for them.
type BlockMapping = Map String VCGBlockInfo

ppBlock :: BlockLabel -> String
ppBlock (Named (Ident s)) = s
ppBlock (Anon i) = show i


data VCGConfig = VCGConfig
  { blockMapping :: !BlockMapping
  , llvmMod      :: !Module
  }


findBlock :: VCGConfig -> BlockLabel -> VCGBlockInfo
findBlock cfg lbl =
  case Map.lookup (ppBlock lbl) (blockMapping cfg) of
    Just blockInfo -> blockInfo
    Nothing -> do
      error $ "Could not find map for block " ++ show lbl

-- | Callback functions for interacting with SMT solver.
data CallbackFns = CallbackFns
  { addCommandCallback :: !(SMT.Command -> IO ())
  , addNegGoalCallback :: !(SMT.Term -> IO ())
  , addGoalCallback :: !(SMT.Term -> IO ())
  }

data PfConfig = PfConfig
  { cfgConfig :: !VCGConfig
    -- ^ The current configuration
  , stackAccesses :: !(Set (MemSegmentOff 64))
    -- ^ Set of instruction addresses in this block accessing the stack.
  , callbackFns :: !CallbackFns
  }

data PfState = PfState
  { mcCurAddr :: !(MemSegmentOff 64)
  , mcMemIndex :: !Integer
  }


-- | Return true if acceses at the current instruction accesses stack.
atStackAddr :: PfConfig -> PfState -> Bool
atStackAddr cfg s = Set.member (mcCurAddr s) (stackAccesses cfg)

type VCGMonad = ReaderT PfConfig (StateT PfState IO)

addCommand :: SMT.Command -> VCGMonad ()
addCommand cmd = do
  fns <- asks callbackFns
  liftIO $ addCommandCallback fns cmd

addNegGoal :: SMT.Term -> VCGMonad ()
addNegGoal g = do
  fns <- asks callbackFns
  liftIO $ addNegGoalCallback fns g

addGoal :: SMT.Term -> VCGMonad ()
addGoal g = do
  fns <- asks callbackFns
  liftIO $ addGoalCallback fns g

addAssert :: SMT.Term -> VCGMonad ()
addAssert p = addCommand $ SMT.assert p

-- | Assert that the functions identified by the LLVM and macaw function pointers
-- are equivalent.
assertFnNameEq :: SMT.Term -> SMT.Term -> VCGMonad ()
assertFnNameEq llvmFun macawIP = undefined llvmFun macawIP

x86ArgRegs :: [X86Reg (M.BVType 64)]
x86ArgRegs = [ RDI, RSI, RDX, RCX, R8, R9 ]

getMacawMem :: VCGMonad SMT.Term
getMacawMem = do
  idx <- gets mcMemIndex
  pure $! varTerm (M.memVar idx)

macawRead :: SMT.Term -> Integer -> Var -> VCGMonad ()
macawRead addr byteCount valVar = do
  mem <- getMacawMem
  let valType = SMT.bvSort (8*byteCount)
  let val | byteCount `elem` [1,2,4,8] =
              SMT.term_app (memReadName byteCount) [mem, addr]
          | otherwise = readBVLE mem addr byteCount
  addCommand $ SMT.defineFun valVar [] valType val

macawWrite :: SMT.Term -> Integer -> SMT.Term -> VCGMonad ()
macawWrite addr byteCount val = do
  idx <- gets mcMemIndex
  modify' $ \s -> s { mcMemIndex = mcMemIndex s + 1 }
  let mem = varTerm (M.memVar idx)
  let newMem | byteCount `elem` [1,2,4,8] =
                 SMT.term_app (memWriteName byteCount) [mem, addr, val]
             | otherwise =
                 writeBVLE (varTerm (M.memVar idx)) addr val byteCount
  addCommand $ SMT.defineFun (M.memVar (idx+1)) [] memSort newMem

-- | A SMT predicate that holds if all the bytes [addr, addr+sz)` is in the current stack frame.
--
-- Note. This predicate can assume that `sz > 0` and `sz < 2^64`, but still
-- be correct if the computation of `addr+sz` overflows.
onThisStackFrame :: SMT.Term -> Integer -> SMT.Term
onThisStackFrame addr sz = SMT.term_app "on_this_stack_frame" [addr, SMT.bvdecimal sz 64]

ptrSort :: SMT.Sort
ptrSort = SMT.bvSort 64

memSort :: SMT.Sort
memSort = SMT.arraySort (SMT.bvSort 64) (SMT.bvSort 8)

onThisStackFrameDecl :: SMT.Command
onThisStackFrameDecl = do
  let args = [("a", ptrSort), ("sz", SMT.bvSort 64)]
  SMT.defineFun "on_this_stack_frame" args SMT.boolSort $
    SMT.letBinder [ ("e", SMT.bvadd (varTerm "a") [varTerm "sz"]) ] $
      SMT.and [ SMT.bvule (varTerm "stack_low") (varTerm "a")
              , SMT.bvule (varTerm "a") (varTerm "e")
              , SMT.bvule (varTerm "e") (varTerm "stack_high")
              ]

memReadName :: (IsString a, Semigroup a) => Integer -> a
memReadName byteCount = "mem_read" <> fromString (show (8*byteCount))

memWriteName :: (IsString a, Semigroup a) => Integer -> a
memWriteName byteCount = "mem_write" <> fromString (show (8*byteCount))

-- | Create mem write declaration given number of bytes to write
memReadDecl :: Integer -> SMT.Command
memReadDecl w = do
  SMT.defineFun (memReadName w) [("m", memSort), ("a", ptrSort)] (SMT.bvSort (8*w)) $
    readBVLE (varTerm "m") (varTerm "a") w

-- | Create mem write declaration given number of bytes to write
memWriteDecl :: Integer -> SMT.Command
memWriteDecl w = do
  let argTypes = [("m", memSort), ("a", ptrSort), ("v", SMT.bvSort (8*w))]
  SMT.defineFun (memWriteName w) argTypes memSort $
    writeBVLE (varTerm "m") (varTerm "a") (varTerm "v") w

comment :: Builder -> SMT.Command
comment r = SMT.Cmd $ "; " <> r

memDecls :: [SMT.Command]
memDecls
  =  fmap memReadDecl  [1,2,4,8]
  ++ fmap memWriteDecl [1,2,4,8]

-- | Declaration for defining current stack frame bounds.
--
-- Note. This assumes X86 regisrters are already declared.
mcStackBoundDecls :: Integer -> [SMT.Command]
mcStackBoundDecls sz = do
  let initRSP = varTerm (M.smtRegVar RSP)
   in [ SMT.defineFun "stack_low"  [] (SMT.bvSort 64)
        (SMT.bvsub initRSP (SMT.bvdecimal sz 64))
      -- High water stack pointer includes 8 bytes for return address.
      , comment "stack_high is the initial stack pointer plus 8 for the return address."
      , SMT.defineFun "stack_high"  [] (SMT.bvSort 64)
        (SMT.bvadd initRSP [SMT.bvdecimal 8 64])
        -- Assert RSP has enough room to hold the return address.
      , SMT.assert $ SMT.bvult initRSP (SMT.bvdecimal (2^(64::Int) - 8) 64)
        -- Assert RSP has enough room to hold the given number of bytes.
      , SMT.assert $ SMT.bvugt initRSP (SMT.bvdecimal sz 64)
      , onThisStackFrameDecl
      ]


-- | Handler for when eventsEq doesn't match events.
eventsDone :: [L.Event] -> [M.Event] -> VCGMonad ()
eventsDone [] [] = pure ()
eventsDone (lev:_) [] = do
  error $ "LLVM after end of Macaw events:\n"
    ++ L.ppEvent lev
eventsDone [] (mev:_) = do
  error $ "Macaw event after end of LLVM events:\n"
    ++ M.ppEvent mev
eventsDone (lev:_) (mev:_) = do
  addr <- gets mcCurAddr
  error $ "Incompatible LLVM and Macaw events:\n"
    ++ "LLVM:  " ++ L.ppEvent lev ++ "\n"
    ++ "Macaw " ++ show addr ++ ": " ++ M.ppEvent mev

eventsEq :: [L.Event]
         -> [M.Event]
         -> VCGMonad ()
eventsEq levs (M.CmdEvent cmd:mevs) = do
  addCommand cmd
  eventsEq levs mevs
eventsEq levs (M.InstructionEvent curAddr:mevs) = do
  modify $ \s -> s { mcCurAddr = curAddr }
  eventsEq levs mevs

eventsEq (L.CmdEvent cmd:levs) mevs = do
  addCommand cmd
  eventsEq levs mevs
eventsEq (L.AllocaEvent{}:levs) mevs =
  eventsEq levs mevs --Skip alloca events
eventsEq levs0 mevs0@(M.ReadEvent macawAddr macawCount macawValVar:mevs) = do
  cfg <- ask
  s <- get
  case levs0 of
    levs | atStackAddr cfg s -> do
      -- Define value from reading Macaw heap
      macawRead macawAddr macawCount macawValVar
      -- Assert address is on stack
      addGoal $ onThisStackFrame macawAddr macawCount
      -- Process future events.
      eventsEq levs mevs
    L.LoadEvent _llvmAddr llvmCount llvmValVar:levs -> do
      -- Define value from reading Macaw heap
      macawRead macawAddr macawCount macawValVar
      -- Check size of writes are equivalent.
      when (macawCount /= llvmCount) $ do
        error "Bytes read with different number of bytes."
      liftIO $ hPutStrLn stderr $ "TODO: Assert addresses are equal."

      -- Define LLVM value returned in terms of macaw value
      addCommand $ SMT.defineFun llvmValVar [] (SMT.bvSort (8*macawCount)) (varTerm macawValVar)
      -- Process future events.
      eventsEq levs mevs
    levs -> do
      eventsDone levs mevs0

eventsEq (L.LoadEvent _llvmAddr llvmCount llvmValVar:levs)
         (M.CondReadEvent macawCond macawReadAddr macawCount _macawDef macawValVar:mevs) = do
  -- Require that write occurs.
  addGoal $ macawCond
  -- Check size of writes are equivalent.
  when (macawCount /= llvmCount) $ do
    error "Bytes read with different number of bytes."
  liftIO $ hPutStrLn stderr $ "TODO: Assert addresses are equal."
  --  addNegGoal $ SMT.distinct [ llvmAddr, macawAddr ]
  -- Define Macaw value returned
  macawRead macawReadAddr macawCount macawValVar
  -- Define LLVM value returned in terms of macaw value
  addCommand $ SMT.defineFun llvmValVar [] (SMT.bvSort (8*macawCount)) (varTerm macawValVar)
  -- Process future events.
  eventsEq levs mevs

-- This doesn't match a LLVM read, so we will require it either
-- doesn't occur or is a write to the stack.
eventsEq levs
         (M.CondReadEvent macawCond addr byteCount defTerm macawValVar:mevs) = do

  -- Declare macaw value variable
  mem <- getMacawMem
  let valType = SMT.bvSort (8*byteCount)
  -- Assert that there are at least byteCount bytes available to read at address addr.
  addGoal $ SMT.implies [macawCond] (onThisStackFrame addr byteCount)

  addCommand $ SMT.defineFun macawValVar [] valType $
     SMT.ite macawCond (readBVLE mem addr byteCount) defTerm

  eventsEq levs mevs

eventsEq levs0 mevs0@(M.WriteEvent macawAddr macawCount macawVal:mevs) = do
  cfg <- ask
  s <- get
  case levs0 of
    -- If we are at a stack address, then do following.
    levs | atStackAddr cfg s -> do
      -- Update stack with write.
      macawWrite macawAddr macawCount macawVal
      -- Assert address is on stack
      addGoal $ onThisStackFrame macawAddr macawCount
      -- Process next events
      eventsEq levs mevs

    L.StoreEvent _llvmAddr llvmCount llvmVal:levs -> do

      when (llvmCount /= macawCount) $ do
        error "Bytes written have different number of bytes."
      liftIO $ hPutStrLn stderr $ "TODO: Assert addresses are equal."

      -- Assert values are equal
      addNegGoal $ SMT.distinct [ llvmVal, macawVal ]

      -- Update macaw memory
      macawWrite macawAddr macawCount macawVal

      eventsEq levs mevs
    levs ->
      eventsDone levs mevs0

eventsEq [L.InvokeEvent _ f lArgs _lRet] [M.FetchAndExecuteEvent regs] = do
  let Const mRegIP = regs ^. boundValue X86_IP
  assertFnNameEq f mRegIP
  -- Verify that the arguments should be same.
  -- Note: Here we take the number of arguments from LLVM side,
  -- since the number of arguments in Macaw side seems not explicit.
  -- Also assuming that the # of arguments of LLVM side is less or equal than six.
  when (length lArgs > length x86ArgRegs) $ do
    error $ "Too many arguments."

  let compareArg :: SMT.Term -> X86Reg (M.BVType 64) -> VCGMonad ()
      compareArg la reg = do
        let Const ma = regs^.boundValue reg
        addNegGoal (SMT.distinct [la, ma])
  zipWithM_ compareArg lArgs x86ArgRegs
eventsEq [L.JumpEvent lbl] [M.FetchAndExecuteEvent regs] = do
  cfg <- asks $ cfgConfig
  let blockInfo = findBlock cfg lbl
  -- Get term for address associated with this label.
  let llvmMemAddr = SMT.bvdecimal (toInteger (blockAddr blockInfo)) 64
  let Const mRegIP = regs ^. boundValue X86_IP
  addNegGoal (SMT.distinct [llvmMemAddr, mRegIP])
  liftIO $ hPutStrLn stderr $ "TODO: Assert preconditions for block."
eventsEq [L.ReturnEvent mlret] [M.FetchAndExecuteEvent regs] = do
  case mlret of
    Nothing -> pure ()
    Just lret -> do
      let Const mret = regs^.boundValue RAX
      addNegGoal (SMT.distinct [lret, mret])
eventsEq levs mevs = eventsDone levs mevs


{-
retValugeEq :: IsSymExprBuilder sym
           => sym -> Maybe (SymBV64 sym) -> Maybe (SymBV64 sym)
           -> VCGMonad sym ids ()
retValueEq sym (Just bv1) (Just bv2) = do
  eq <- liftIO $ bvEq sym bv1 bv2
  addProofGoal sym eq
retValueEq _sym (Just _) _ = do
  liftIO $ warning "LLVM block does not have return value, proof failed"
retValueEq _sym _ (Just _) = do
  liftIO $ warning "Macaw block does not have return value, proof failed"
retValueEq _sym _ _ = do
  liftIO $ warning "return value is not provided"
-}

{-
simulateAndCheck :: IsSymExprBuilder sym
                 => sym
                 -> VCGFunInfo
                 -> BasicBlock
                 -> DiscoveryFunInfo X86_64 ids
                 -> L.LState sym
                 -> M.MState sym ids
                 -> VCGMonad sym ids ()
simulateAndCheck sym _vfi bb discInfo ls0 ms0 = do
  liftIO $ putStrLn "Simulating LLVM program ..."
  ls' <- liftIO $ execStateT (L.bb2SMT sym bb) ls0

  liftIO $ putStrLn "Simulating Macaw program ..."
  ms' <- liftIO $ execStateT (M.blocks2SMT sym discInfo) ms0

  -- Build disjointness constraints and variable mapping constraints,
  -- which will be used as pre-conditions
  disCons <- liftIO $  disjointConstraints sym ls' ms'
  addProofPreConds sym disCons

  -- Check state equality
  stateEq sym ls' ms'
-}

forceResolveAddr :: Memory w -> MemWord w -> MemSegmentOff w
forceResolveAddr mem a =
  case resolveAbsoluteAddr mem a of
    Just segOff -> segOff
    Nothing -> error $ "Could not resolve " ++ show a

extractStackAddresses :: Memory 64 -> BlockEvent -> Maybe (MemSegmentOff 64)
extractStackAddresses mem evt =
  case eventType evt of
    StackRegRead -> Just $ forceResolveAddr mem (fromInteger (eventAddr evt))
    StackRegWrite -> Just $ forceResolveAddr mem (fromInteger (eventAddr evt))

reportSMTErrors :: Handle -> IO ()
reportSMTErrors h = forever $ do
  msg <- hGetLine h
  hPutStrLn stderr $ "Solver: " ++ msg

cleanup :: ProcessHandle -> ThreadId -> IO ()
cleanup ph tid = do
  killThread tid
  terminateProcess ph

interactiveVerifyGoal :: String -- ^ Name of function to verify
                      -> BlockLabel -- ^ Label of block
                      -> IORef Integer -- ^ Index of goal to discharge within block
                      -> Handle -- ^ Command handle
                      -> Handle -- ^ Response handle
                      -> SMT.Term
                         -- ^ Negation of goal to verify
                      -> IO ()
interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle ng =do
  cnt <- readIORef goalCounter
  modifyIORef' goalCounter (+1)
  let fname = standaloneGoalFilename funName lbl cnt
  hPutStrLn stderr $ "Sending check-sat command"
  writeCommand cmdHandle $ SMT.checkSatAssuming [ng]
  hFlush cmdHandle
  hPutStrLn stderr $ "Waiting for response"
  resp <- SMTP.readCheckSatResponse respHandle
  case resp of
    SMTP.SatResponse -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "To see output, run reopt-vcg in standalone mode."
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.UnsatResponse -> do
      hPutStrLn stdout $ "Verified " ++ fname
    SMTP.UnknownResponse -> do
      hPutStrLn stderr $ "Unknown verification result"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "To see output, run reopt-vcg in standalone mode."
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.CheckSatUnsupported -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver does not support check-sat-assuming."
    (SMTP.CheckSatError msg) -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver returned the following message after check-sat-assuming:"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "  " ++ msg




runCallbacks :: String -- ^ Command line
             -> String -- ^ Name of function
             -> BlockLabel
             -> (CallbackFns -> IO a)
             -> IO a
runCallbacks cmdline funName lbl action = do
  goalCounter <- newIORef 0
  let cp = (shell cmdline)
         { std_in = CreatePipe
         , std_out = CreatePipe
         , std_err = CreatePipe
         }
  createResult <- try $ createProcess cp
  case createResult of
    Right (Just cmdHandle, Just respHandle, Just errHandle, ph) -> do
      errThread <- forkIO $ reportSMTErrors errHandle
      flip finally (cleanup ph errThread) $ do
        writeCommand cmdHandle $ SMT.setLogic SMT.allSupported
        writeCommand cmdHandle $ SMT.setProduceModels True
        let fns = CallbackFns
              { addCommandCallback = \cmd -> do
                  writeCommand cmdHandle cmd
              , addNegGoalCallback = \ng -> do
                  interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle ng
              , addGoalCallback = \g -> do
                  interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle (SMT.not g)
              }
        action fns
    Right _ -> do
      hPutStrLn stderr $ "Unexpected failure running " ++ cmdline
      exitFailure
    Left err -> do
      hPutStrLn stderr $ "Could not execute " ++ cmdline
      hPutStrLn stderr $ "  " ++ show (err :: IOException)
      exitFailure

type FunctionName = String

newtype CallbackGenerator
   = CBG { blockCallbacks :: forall a . FunctionName -> BlockLabel -> (CallbackFns -> IO a) -> IO a }

exportCallbacks :: FilePath
                   -- ^ Directory to run file to.
                -> String -- ^ Name of function
                -> BlockLabel
                -> (CallbackFns -> IO a)
                -> IO a
exportCallbacks outDir fn lbl action = do
  goalCounter <- newIORef 0
  cmdRef <- newIORef [] :: IO (IORef [SMT.Command])
  action $! CallbackFns
    { addCommandCallback = \cmd -> do
        modifyIORef' cmdRef $ (cmd:)
    , addNegGoalCallback = \ng -> do
        cnt <- readIORef goalCounter
        modifyIORef' goalCounter (+1)
        cmds <- readIORef cmdRef
        let fname = standaloneGoalFilename fn lbl cnt
        verifyGoal outDir fname cmds ng
    , addGoalCallback = \g -> do
        cnt <- readIORef goalCounter
        modifyIORef' goalCounter (+1)
        cmds <- readIORef cmdRef
        let fname = standaloneGoalFilename fn lbl cnt
        verifyGoal outDir fname cmds (SMT.not g)
    }

runVCGs :: CallbackFns
       -> VCGConfig
       -> Memory 64
       -> BlockLabel
       -> MemSegmentOff 64
          -- ^ Address of first instruction in this block.
       -> VCGMonad ()
       -> IO ()
runVCGs fns cfg mem lbl addr action = do
  let thisBlockCfg = findBlock cfg lbl
  let pfCfg = PfConfig { cfgConfig = cfg
                       , stackAccesses
                         = Set.fromList
                         $ mapMaybe (extractStackAddresses mem)
                         $ blockEvents thisBlockCfg
                       , callbackFns = fns
                       }
  let s = PfState { mcCurAddr = addr
                  , mcMemIndex = 0
                  }
  evalStateT (runReaderT action pfCfg) s

data VerificationMode
   = DefaultMode
   | ExportMode !FilePath
   | RunSolver !String

isDefault :: VerificationMode -> Bool
isDefault DefaultMode = True
isDefault _ = False

data VCGArgs
   = VCGArgs { reoptYaml :: !(Maybe FilePath)
               -- ^ Location with yaml file.
             , requestedMode :: !VerificationMode
             }

data VCGCommand
  = ShowHelp
  | RunVCG !VCGArgs

parseArgs :: [String] -> VCGArgs -> Except String VCGCommand
parseArgs cmdArgs args = seq args $
  case cmdArgs of
    [] -> pure $! RunVCG args
    ("--help":_) -> pure $! ShowHelp
    ("--export":path:rest) -> do
      unless (isDefault (requestedMode args)) $ do
        throwError $ "Cannot specify --export or --solver multiple times."
      parseArgs rest $ args { requestedMode = ExportMode path }
    ("--solver":cmdline:rest) -> do
      unless (isDefault (requestedMode args)) $ do
        throwError $ "Cannot specify --export or --solver multiple times."
      parseArgs rest $ args { requestedMode = RunSolver cmdline }
    (path:rest) -> do
      when ("--" `isPrefixOf` path) $ do
        throwError $ "Unexpected flag " ++ path
      when (isJust (reoptYaml args)) $ do
        throwError $ "Multiple VCG files specified."
      parseArgs rest $ args { reoptYaml = Just path }

showHelp :: IO ()
showHelp = do
  putStrLn
    $  "reopt-vcg generates verification conditions to prove that reopt generated\n"
    ++ "   LLVM is faithful to the input binary.\n"
    ++ "Usage: reopt-vcg <input.yaml> {--export <export-dir> | --solver <solver-path>}"

showError :: String -> IO a
showError msg = do
  hPutStrLn stderr $ "Error: " ++ msg
  hPutStrLn stderr $ "Run `reopt-vcg --help` for additional information."
  exitFailure

parseVCGArgs :: IO (MetaVCGConfig, CallbackGenerator)
parseVCGArgs = do
  cmdArgs <- getArgs
  let initVCG = VCGArgs { reoptYaml = Nothing, requestedMode = DefaultMode }
  args <-
    case runExcept (parseArgs cmdArgs initVCG) of
      Left msg ->
        showError msg
      Right ShowHelp -> do
        showHelp
        exitSuccess
      Right (RunVCG a) -> pure a

  cfg <- do
    -- Get path to YAML
    vcgPath <-
      case reoptYaml args of
        Nothing -> showError "Missing VCG file to run."
        Just path -> return path
    vcgResult <- Yaml.decodeFileWithWarnings vcgPath
    case vcgResult of
      Left err -> do
        hPutStrLn stderr $ "Error parsing Yaml: " ++ show err
        exitFailure
      Right (warnings, cfg) -> do
        when (not (null warnings)) $ do
          hPutStrLn stderr $ "Warnings when parsing Yaml file:"
          forM_ warnings $ \warn -> do
            hPutStrLn stderr $ "  " ++ show warn
          exitFailure
        pure cfg

  gen <-
    case requestedMode args of
      DefaultMode ->
        pure $ CBG $ runCallbacks "cvc4 --lang=smt2" --incremental"
      ExportMode outdir -> do
        r <- try $ createDirectoryIfMissing True outdir
        case r of
          Right () -> do
            putStrLn $ "Writing output to " ++ outdir
            pure $ CBG $ exportCallbacks outdir
          Left e -> do
            hPutStrLn stderr $ "Error creating output directory: " ++ outdir
            hPutStrLn stderr $ "  " ++ show (e :: IOError)
            exitFailure
      RunSolver cmdline ->
        pure $ CBG $ runCallbacks cmdline

  pure (cfg, gen)

-- | Emit an SMT command to the solver.
writeCommand :: Handle -> SMT.Command -> IO ()
writeCommand h (SMT.Cmd b) =
  LText.hPutStrLn h (Builder.toLazyText b)

standaloneGoalFilename :: String -- ^ Name of function to verify
                       -> BlockLabel -- ^ Label of block
                       -> Integer -- ^ Index of goal to discharge within block
                       -> FilePath
standaloneGoalFilename fn lbl i =
 fn ++ "_" ++ ppBlock lbl ++ "_" ++ show i ++ ".smt2"

verifyGoal :: FilePath
           -> FilePath
           -> [SMT.Command]
           -> SMT.Term -> IO ()
verifyGoal outDir fname cmds negGoal = do
  hPutStrLn stdout $ "Writing goal to " ++ show fname
  bracket (openFile (outDir </> fname) WriteMode) hClose $ \h -> do
    writeCommand h $ SMT.setLogic SMT.allSupported
    writeCommand h $ SMT.setProduceModels True
    -- Write commands from proof state
    mapM_ (writeCommand h) (reverse cmds)
    writeCommand h $ SMT.checkSatAssuming [negGoal]
    writeCommand h $ SMT.exit

verifyFunction :: Module
               -> Memory 64
               -> Map BSC.ByteString (MemSegmentOff 64)
                  -- ^ Maps symbol names to addresses
                  --
                  -- Used so user-generated verification files can refer to names rather than addresses.
               -> CallbackGenerator
               -> VCGFunInfo
               -> IO ()
verifyFunction lMod mem funMap gen vfi = do

  let llvmBlockMap :: Map String VCGBlockInfo
      llvmBlockMap = Map.fromList
        [ (blockLabel b, b) | b <- blocks vfi ]
  addr <-
    case Map.lookup (BSC.pack (macawFunName vfi)) funMap of
      Just addr ->
        pure addr
      Nothing ->
        fatalError
            $  "Unknown Macaw function: " ++ macawFunName vfi ++ "\n"
            ++ "Available functions:\n"
            ++ unlines ((\x -> "  " ++ BSC.unpack x) <$> Map.keys funMap)

  hPutStrLn stderr $ "Analyzing " ++ macawFunName vfi

  let Just lFun = L.getDefineByName lMod (llvmFunName vfi)

  (firstBlock, restBlocks) <-
    case defBody lFun of
      [] -> error $ "Expected function to have at least one basic block."
      f:r -> pure (f,r)

  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."

  let Just lbl = bbLabel firstBlock
  blockCallbacks gen (llvmFunName vfi) lbl $ \fns -> do
    let vcgCfg =  VCGConfig { blockMapping = llvmBlockMap
                            , llvmMod = lMod
                            }
    let blockInfo = findBlock vcgCfg lbl

    --TODO: Check block address
    --when (blockAddr blockInfo /= addr) $ do
    --  error "Block annotation does not have correct address."

    putStrLn "Simulating LLVM blocks ..."
    levents <- do
      do let ?config = Config True True True
         putStrLn $ show $ ppBasicBlock firstBlock
      let ls0 = L.inject lFun
      reverse . L.events <$> execStateT (L.bb2SMT firstBlock) ls0
    putStrLn $ "LLVM events:  " ++ show levents

    putStrLn "Simulating Macaw blocks ..."
    mevents <- M.blockEvents addr (blockSize blockInfo)
    putStrLn $ "Macaw events: " ++ show mevents


    -- Assert arguments are equal
    runVCGs fns vcgCfg mem lbl addr $ do
      mapM_ addCommand memDecls
      mapM_ addCommand M.declRegs

      when (stackSize vfi < 0) $ do
        error "Expected non-negative stack size"

      addCommand $ SMT.declareFun (M.memVar 0) [] memSort
      mapM_ addCommand $ mcStackBoundDecls (stackSize vfi)

      let mkLLVMDecl :: Typed Ident -> VCGMonad ()
          mkLLVMDecl (Typed (PrimType (Integer 64)) val) =
            addCommand $ SMT.declareFun (L.identVar val) [] (SMT.bvSort 64)
          mkLLVMDecl  (Typed tp _) =
            error $ "Unexpected type " ++ show tp
      mapM_ mkLLVMDecl $ defArgs lFun
      let assertEq lv reg = do
            addAssert $ SMT.eq [varTerm (L.identVar (typedValue lv)), varTerm (M.smtRegVar reg)]
      zipWithM_ assertEq (defArgs lFun) x86ArgRegs
      eventsEq levents mevents

    -- write proof to smt file

  forM_ restBlocks $ \_bb -> do
    pure ()


-- | Read an elf from a binary
readElf :: FilePath -> IO (Elf 64)
readElf path = do
  contents <- BS.readFile path
  case parseElf contents of
    ElfHeaderError _ msg ->
      fatalError msg
    Elf32Res{} -> do
      fatalError "Expected 64-bit elf file."
    Elf64Res errs e -> do
      mapM_ (warning . show) errs
      unless (elfMachine e == EM_X86_64) $ do
        fatalError "Expected a x86-64 binary"
      unless (elfOSABI e `elem` [ELFOSABI_LINUX, ELFOSABI_SYSV]) $ do
        warning "Expected Linux binary"
      pure e

main :: IO ()
main = do
  (metaCfg, gen) <- parseVCGArgs
  putStrLn $ show metaCfg
  e <- readElf $ binFilePath metaCfg
  let loadOpts = defaultLoadOptions
  case resolveElfContents loadOpts e of
    Left err -> do
      hPutStrLn stderr $
        "Could not interpret Elf file " ++ binFilePath metaCfg ++ ":\n"
        ++ "  " ++ err
      exitFailure
    Right (warnings, mem, _entry, symbols) -> do
      forM_ warnings $ \w -> do
        hPutStrLn stderr w
      lMod <- L.getLLVMMod (llvmBCFilePath metaCfg)
      let funMap = Map.fromList [ (memSymbolName msym, memSymbolStart msym) | msym <- symbols ]
      forM_ (functions metaCfg) $ \vfi -> do
        verifyFunction lMod mem funMap gen vfi
