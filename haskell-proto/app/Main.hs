{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (MetaVCGConfig(..), main) where

import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad (forM_)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import qualified Data.ByteString.Char8 as BSC
import           Data.List as List
import qualified Data.Macaw.Architecture.Info as M
import           Data.Macaw.CFG
import           Data.Macaw.Discovery
import qualified Data.Macaw.Types as M
import           Data.Macaw.X86
import           Data.Macaw.X86.X86Reg
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import qualified Data.Text as Text
import qualified Data.Yaml as Yaml
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           Text.LLVM hiding ((:>), Value)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as LText
import           Text.LLVM.PP
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import           Reopt.VCG.Config
import           VCGCommon
import qualified VCGLLVM as L
import qualified VCGMacaw as M


-- Maps LLVM block labels to the Macaw adddress they are associated with.
type BlockMapping = Map BlockLabel (MemSegmentOff 64)

data VCGConfig = VCGConfig
  { blockMapping :: !BlockMapping
  , llvmMod      :: Module
  }

data PfState = PfState
  { pfCmds :: [SMT.Command]
    -- ^ Commands added when traversing events in reverse order.
  , negGoals :: [([SMT.Command], SMT.Term)]
    -- ^ Negation of a goal to prove align with assumptions up to goal.
  , macawMemIndex :: !Integer
  }

type VCGMonad = ReaderT VCGConfig (StateT PfState IO)

addCommand :: SMT.Command -> VCGMonad ()
addCommand cmd = modify $ \s -> s { pfCmds = cmd : pfCmds s }

addAssumption :: SMT.Term -> VCGMonad ()
addAssumption p = addCommand $ SMT.assert p

addNegGoal :: SMT.Term -> VCGMonad ()
addNegGoal g = do
  s <- get
  let cmds = pfCmds s
  put $ s { negGoals = (cmds, g) : negGoals s }

-- | Assert that the functions identified by the LLVM and macaw function pointers
-- are equivalent.
assertFnNameEq :: SMT.Term -> SMT.Term -> VCGMonad ()
assertFnNameEq llvmFun macawIP = undefined llvmFun macawIP

x86ArgRegs :: [X86Reg (M.BVType 64)]
x86ArgRegs = [ RDI, RSI, RDX, RCX, R8, R9 ]

evalMemAddr :: Map RegionIndex SMT.Term
            -> MemAddr 64
            -> SMT.Term
evalMemAddr m a =
  case Map.lookup (addrBase a) m of
    Nothing -> error "evalMemAddr given address with bad region index."
    Just b -> SMT.bvadd b [SMT.bvdecimal (toInteger (addrOffset a)) 64]

macawRead :: SMT.Term -> Integer -> Var -> VCGMonad ()
macawRead addr byteCount valVar = do
  idx <- gets macawMemIndex
  let mem = SMem (varTerm (M.memVar idx))
  let valType = SMT.bvType (8*byteCount)
  addCommand $ SMT.defineFun valVar [] valType (readBVLE mem addr byteCount)


macawWrite :: SMT.Term -> Integer -> SMT.Term -> VCGMonad ()
macawWrite addr byteCount val = do
  idx <- gets macawMemIndex
  let mem = SMem (varTerm (M.memVar idx))
  let SMem newMem = writeBVLE mem addr val byteCount
  addCommand $ SMT.defineFun (M.memVar (idx+1)) [] memType newMem
  modify $ \s -> s { macawMemIndex = idx + 1 }

eventsEq :: [L.LEvent]
         -> [M.MEvent]
         -> VCGMonad ()
eventsEq [] [] = return ()
eventsEq (L.CmdEvent cmd:levs) mevs = do
  addCommand cmd
  eventsEq levs mevs
eventsEq levs (M.CmdEvent cmd:mevs) = do
  addCommand cmd
  eventsEq levs mevs
eventsEq (L.AllocaEvent{}:levs) mevs =
  eventsEq levs mevs --Skip alloca events
eventsEq (L.LoadEvent _llvmAddr llvmCount llvmValVar:levs)
         (M.CondReadEvent macawCond macawAddr macawCount macawValVar:mevs) = do
  when (macawCount /= llvmCount) $ do
    error "Bytes read with different number of bytes."
  let valType = SMT.bvType (8*macawCount)
  liftIO $ hPutStrLn stderr $ "TODO: Assert addresses are equal."

  -- Require that write occur.
  addNegGoal $ SMT.not macawCond

  -- Assert addresses correspond equal
--  addNegGoal $ SMT.distinct [ llvmAddr, macawAddr ]

  -- Declare values returned and assert they are equal.
  addCommand $ SMT.declareFun llvmValVar [] valType
  macawRead macawAddr macawCount macawValVar
  addAssumption $ SMT.eq [ varTerm llvmValVar, varTerm macawValVar]
  eventsEq levs mevs

eventsEq levs
         (M.CondReadEvent macawCond addr byteCount macawValVar:mevs) = do

  let valType = SMT.bvType (8*byteCount)
  liftIO $ hPutStrLn stderr $ "TODO: Assert address is on stack and valid."

  -- Declare macaw value variable
  idx <- gets macawMemIndex
  let mem = SMem (varTerm (M.memVar idx))
  addCommand $ SMT.declareFun macawValVar [] valType

  addAssumption $ SMT.implies [macawCond] (SMT.eq [ varTerm macawValVar, readBVLE mem addr byteCount])
  eventsEq levs mevs

eventsEq (L.StoreEvent _llvmAddr llvmCount llvmVal:levs)
         (M.WriteEvent macawAddr macawCount macawVal:mevs) = do
  when (llvmCount /= macawCount) $ do
    error "Bytes written have different number of bytes."
  liftIO $ hPutStrLn stderr $ "TODO: Assert addresses are equal."

  -- Assert values are equal
  addNegGoal $ SMT.distinct [ llvmVal, macawVal ]

  -- Assert addresses correspond equal
--  addNegGoal $ SMT.distinct [ llvmAddr, macawAddr ]

  -- Update macaw memory
  macawWrite macawAddr macawCount macawVal

  eventsEq levs mevs

-- Writes to the stack may occur in Macaw, but not LLVM
eventsEq levs (M.WriteEvent macawAddr macawCount macawVal:mevs) = do
  liftIO $ hPutStrLn stderr $ "TODO: Assert address is on stack."

  macawWrite macawAddr macawCount macawVal


  -- Assert addresses correspond equal
--  addNegGoal $ SMT.distinct [ llvmAddr, macawAddr ]

  eventsEq levs mevs



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
  m <- asks blockMapping
  case Map.lookup lbl m of
    Just off -> do
      let regionMap = error "region index map is not defined."
      let llvmMemAddr = evalMemAddr regionMap (relativeSegmentAddr off)
      let Const mRegIP = regs ^. boundValue X86_IP
      addNegGoal (SMT.distinct [llvmMemAddr, mRegIP])
    Nothing -> do
      error $ "Could not find map for block " ++ show lbl
eventsEq [L.ReturnEvent mlret] [M.FetchAndExecuteEvent regs] = do
  case mlret of
    Nothing -> pure ()
    Just lret -> do
      let Const mret = regs^.boundValue RAX
      addNegGoal (SMT.distinct [lret, mret])
eventsEq (lev:_) [] = do
  error $ "LLVM after end of Macaw events:\n"
    ++ L.ppEvent lev
eventsEq [] (mev:_) = do
  error $ "Macaw event after end of LLVM events:\n"
    ++ M.ppEvent mev
eventsEq (lev:_) (mev:_) = do
  error $ "Incompatible LLVM and Macaw events:\n"
    ++ "LLVM:  " ++ L.ppEvent lev ++ "\n"
    ++ "Macaw: " ++ M.ppEvent mev




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

stateEq :: L.LState
        -> M.MState
        -> VCGMonad ()
stateEq lstate mstate = do
  -- Check event traces equality
  let levs = reverse $ L.events lstate
  let mevs = reverse $ M.events mstate
  eventsEq levs mevs

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

runVCG :: VCGConfig -> [SMT.Command] -> VCGMonad () -> IO PfState
runVCG cfg cmds action =
  let s = PfState { pfCmds
                      =  [SMT.declareFun (M.memVar 0) [] memType  ]
                      ++ reverse cmds
                  , negGoals = []
                  , macawMemIndex = 0
                  }
   in execStateT (runReaderT action cfg) s

data VCGArgs
   = VCGArgs { reoptYaml :: !(Maybe FilePath)
               -- ^ Location with
             , outputDir :: !(Maybe FilePath)
               -- ^ Where to write output.
             }

data VCGCommand
  = ShowHelp
  | RunVCG !VCGArgs

parseArgs :: [String] -> VCGArgs -> Except String VCGCommand
parseArgs cmdArgs args = seq args $
  case cmdArgs of
    [] -> pure $! RunVCG args
    ("--help":_) -> pure $! ShowHelp
    ("--output":path:rest) -> do
      when (isJust (outputDir args)) $ do
        throwError $ "Output directory defined multiple times."
      parseArgs rest $ args { outputDir = Just path }
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
    ++ "Usage: reopt-vcg <input.yaml> --output <out-dir>"

showError :: String -> IO a
showError msg = do
  hPutStrLn stderr $ "Error: " ++ msg
  hPutStrLn stderr $ "Run `reopt-vcg --help` for additional information."
  exitFailure

parseVCGArgs :: IO (MetaVCGConfig, FilePath)
parseVCGArgs = do
  cmdArgs <- getArgs
  let initVCG = VCGArgs { reoptYaml = Nothing, outputDir = Nothing }
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
  let out =
        case outputDir args of
          Just d  -> d
          Nothing -> replaceExtension (llvmBCFilePath cfg) "vcg"
  r <- try $ createDirectoryIfMissing True out
  case r of
    Right () -> do
      putStrLn $ "Writing output to " ++ out
    Left e -> do
      hPutStrLn stderr $ "Error creating output directory: " ++ out
      hPutStrLn stderr $ "  " ++ show (e :: IOError)
      exitFailure
  pure (cfg, out)


ppBlock :: BlockLabel -> String
ppBlock (Named (Ident s)) = s
ppBlock (Anon i) = show i

{-
verifyBlock :: IO ()
verifyBlock = do
-}

writeCommand :: Handle -> SMT.Command -> IO ()
writeCommand h (SMT.Cmd b) =
  LText.hPutStrLn h (Builder.toLazyText b)

verifyFunction :: Module
               -> DiscoveryState X86_64
               -> Map BSC.ByteString (MemSegmentOff 64)
                  -- ^ Maps symbol names to addresses
                  --
                  -- Used so user-generated verification files can refer to names rather than addresses.
               -> FilePath
               -> VCGFunInfo
               -> IO ()
verifyFunction lMod discState funMap outDir vfi = do
  let mem = memory discState
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

  let mkLLVMDecl :: Typed Ident -> SMT.Command
      mkLLVMDecl arg@(Typed (PrimType (Integer 64)) _) =
        SMT.declareFun (L.argVar arg) [] (SMT.bvType 64)
      mkLLVMDecl  (Typed tp _) =
        error $ "Unexpected type " ++ show tp

  let llvmArgDecls = mkLLVMDecl <$> defArgs lFun

  let mkLLVMArg :: Typed Ident -> SMT.Term
      mkLLVMArg = varTerm . L.argVar

  let llvmVals :: [SMT.Term]
      llvmVals     = mkLLVMArg <$> defArgs lFun

  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."

  Some stGen <- liftIO $ stToIO $ newSTNonceGenerator

  let ls0 = L.inject $ zip (typedValue <$> defArgs lFun) llvmVals
  let ms0 = M.inject


  let vcgCfg =  VCGConfig { blockMapping = Map.empty
                          , llvmMod = lMod
                          }
  putStrLn "Simulating LLVM program ..."
  do let ?config = Config True True True
     putStrLn $ show $ ppBasicBlock firstBlock
  ls' <- execStateT (L.bb2SMT firstBlock) ls0
  putStrLn "Simulating Macaw program ..."
  let initAbsState = M.mkInitialAbsState x86_64_linux_info mem addr
  (blocks,_cnt, _merr) <- stToIO $
    M.disassembleFn x86_64_linux_info stGen addr maxBound initAbsState
  let blockMap = Map.fromList [ (M.blockLabel b, b) | b <- blocks ]
  let Just macawParsedBlock = Map.lookup 0 blockMap
  ms' <- execStateT (M.block2SMT blockMap macawParsedBlock) ms0
  pfSt <- runVCG vcgCfg llvmArgDecls $ stateEq ls' ms'

  -- write proof to smt file
  putStrLn $ "Writing SMT formulas to " ++ outDir
  let Just lbl = bbLabel firstBlock
  forM_ (zip [0..] (reverse (negGoals pfSt))) $ \(i, (cmds, negGoal)) -> do
    let fname = llvmFunName vfi ++ "_" ++ ppBlock lbl ++ "_" ++ show (i::Integer) ++ ".smt"
    bracket (openFile (outDir </> fname) WriteMode) hClose $ \h -> do
      writeCommand h $ SMT.setLogic SMT.allSupported
      writeCommand h $ SMT.setOption (SMT.produceModels True)

      -- Write commands from proof state
      mapM_ (writeCommand h) (reverse cmds)

      -- Assert arguments are equal
      let assertEq lv reg = do
            let Const mv = M.initRegs ms0^.boundValue reg
            writeCommand h $ SMT.assert $ SMT.eq [lv, mv]
      zipWithM_ assertEq llvmVals x86ArgRegs


      writeCommand h $ SMT.assert negGoal
      writeCommand h $ SMT.checkSat
      writeCommand h $ SMT.exit

  forM_ restBlocks $ \_bb -> do
    pure ()


main :: IO ()
main = do
  (metaCfg, outDir) <- parseVCGArgs
  putStrLn $ show metaCfg
  mDiscState <- M.getDiscState $ binFilePath metaCfg
  lMod <- L.getLLVMMod (llvmBCFilePath metaCfg)
  let funMap = Map.fromList [ (sym, addr) | (addr,sym) <- Map.toList $ symbolNames mDiscState ]
  forM_ (functions metaCfg) $ \vfi -> do
    verifyFunction lMod mDiscState funMap outDir vfi
