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
import qualified Data.Yaml as Yaml
import           Lang.Crucible.Backend.Simple
import           System.Directory
import qualified Data.Text as Text
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           Text.LLVM hiding ((:>), Value)
import           What4.Expr.Builder (getSymbolVarBimap)
import           What4.Interface
import qualified What4.Protocol.SMTLib2 as SMT2
import qualified What4.Protocol.SMTWriter as SMT2 (mkSMTTerm)
import           What4.Solver.CVC4

import           Reopt.VCG.Config

import           VCGCommon
import qualified VCGLLVM as L
import qualified VCGMacaw as M
import           Text.LLVM.PP

import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as LText
import qualified What4.Protocol.SMTLib2.Syntax as SMT

-- Maps LLVM block labels to the Macaw adddress they are associated with.
type BlockMapping = Map BlockLabel (MemSegmentOff 64)

data VCGConfig sym ids = VCGConfig
  { blockMapping :: !BlockMapping
  , llvmMod      :: Module
  , exprBuilder  :: sym
  , symIsBuilder :: (forall a . (IsSymExprBuilder sym => a) -> a)
  }

type Prop sym = (SMT.Term, SymBV sym 64)

data PfState sym = PfState
  { pfCmds :: [SMT.Command]
    -- ^ Commands added when traversing events in reverse order.
  , preConds :: [Prop sym]
  , goals :: [Prop sym]
  }

type VCGMonad sym ids = ReaderT (VCGConfig sym ids) (StateT (PfState sym) IO)

proveLLVMAndMacawEq :: SMT.Term -> SymBV sym 64 -> VCGMonad sym ids ()
proveLLVMAndMacawEq la ma = do
  modify $ \s -> s { goals = (la, ma) : goals s }

assumeValEq :: SMT.Term -> SymBV sym 64 -> VCGMonad sym ids ()
assumeValEq lRetVal mRetVal = do
  modify $ \s -> s { preConds = (lRetVal, mRetVal) : preConds s }

{-
-- | Insert a false predicate to make sure the proof fail
proofFailed :: IsSymExprBuilder sym => sym -> VCGMonad sym ids ()
proofFailed sym = do
  liftIO $ putStrLn "Warning: proof failed."
  addProofGoal sym (falsePred sym)
-}

{-
-- | Return true if the givne LLVM blocklabel corresponds with the address of the x86 block.
matchLabel :: BlockMapping
           -> BlockLabel
           -> MemSegmentOff 64
           -> Bool
matchLabel m llbl mlbl =
  case Map.lookup llbl m of
    Just massoc -> mlbl == massoc
    Nothing -> error $ "No association for " ++ show llbl
-}

{-
jumpEventEq :: IsSymExprBuilder sym
            => sym
            -> L.LEvent sym
            -> M.MEvent sym ids
            -> VCGMonad sym ids ()
-- Conditional jumps
jumpEventEq sym (L.BranchEvent lcnd tlbl flbl) (M.BranchEvent mcnd (toff,_tregs) (foff,_fregs)) = do
  bm <- asks blockMapping
  pred1 <-
    if matchLabel bm tlbl toff && matchLabel bm flbl foff then
      liftIO $ isEq sym lcnd mcnd
     else
      pure $! falsePred sym
  pred2 <-
    if matchLabel bm tlbl foff && matchLabel bm flbl toff then
      liftIO $ isEq sym lcnd mcnd
     else
      pure $! falsePred sym
  -- TODO: Check registers
  p <- liftIO $ orPred sym pred1 pred2
  addProofGoal sym p
-- Unconditional jumps
jumpEventEq sym (L.JumpEvent lbl) (M.JumpEvent offset _) = do
  m <- asks blockMapping
  case Map.lookup lbl m of
    Just off' -> do
      when (off' /= offset) $ do
        proofFailed sym
    Nothing -> do
      error $ "Could not find map for block " ++ show lbl
jumpEventEq sym _ _ = proofFailed sym
-}

-- | Assert that the functions identified by the LLVM and macaw function pointers
-- are equivalent.
assertFnNameEq :: SMT.Term -> SymBV sym 64 -> VCGMonad sym ids ()
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

eventsEq :: forall sym ids
         .  IsSymExprBuilder sym
         => sym
         -> [L.LEvent]
         -> [M.MEvent sym]
         -> VCGMonad sym ids ()
eventsEq _sym [] [] = return ()
eventsEq sym (L.CmdEvent cmd:levs) mevs = do
  modify $ \s -> s { pfCmds = cmd : pfCmds s }
  eventsEq sym levs mevs
eventsEq sym (L.AllocaEvent{}:levs) mevs =
  eventsEq sym levs mevs --Skip alloca events
--eventsEq sym levs (M.AllocaEvent{}:mevs) =
--  eventsEq sym levs mevs --Skip alloca events
eventsEq sym (L.InvokeEvent _ f lArgs lRet:levs)
             (M.FetchAndExecuteEvent regs:mevs) = do
  let M.MSymExpr mRegIP = regs ^. boundValue X86_IP
  assertFnNameEq f mRegIP
  -- Verify that the arguments should be same.
  -- Note: Here we take the number of arguments from LLVM side,
  -- since the number of arguments in Macaw side seems not explicit.
  -- Also assuming that the # of arguments of LLVM side is less or equal than six.
  when (length lArgs > length x86ArgRegs) $ do
    error $ "Too many arguments."

  let compareArg :: SMT.Term -> X86Reg (M.BVType 64) -> VCGMonad sym ids ()
      compareArg la reg = do
        let M.MSymExpr ma = regs^.boundValue reg
        proveLLVMAndMacawEq la ma
  zipWithM_ compareArg lArgs x86ArgRegs
  -- If LLVM side has a return value, then we assert lRet = mRet as precondition
  -- for the rest program.
  case lRet of
    Just (_id, lRetVal) -> do
      let M.MSymExpr mRetVal = regs^.boundValue RAX
      -- We can assume return values are equal.
      assumeValEq lRetVal mRetVal
    Nothing -> pure ()
  eventsEq sym levs mevs
eventsEq sym (L.JumpEvent lbl:levs) (M.FetchAndExecuteEvent regs:mevs) = do
  m <- asks blockMapping
  case Map.lookup lbl m of
    Just off -> do
      let regionMap = error "region index map is not defined."
      let llvmMemAddr = evalMemAddr regionMap (relativeSegmentAddr off)
      let M.MSymExpr mRegIP = regs ^. boundValue X86_IP
      proveLLVMAndMacawEq llvmMemAddr mRegIP

    Nothing -> do
      error $ "Could not find map for block " ++ show lbl
  eventsEq sym levs mevs
eventsEq sym (L.ReturnEvent mlret:levs) (M.FetchAndExecuteEvent regs:mevs) = do
  case mlret of
    Nothing -> pure ()
    Just lret -> do
      let M.MSymExpr mret = regs^.boundValue RAX
      proveLLVMAndMacawEq lret mret
  eventsEq sym levs mevs
eventsEq _ (lev:_) [] = do
  error $ "LLVM after end of Macaw events:\n"
    ++ L.ppEvent lev
eventsEq _ [] (mev:_) = do
  error $ "Macaw event after end of LLVM events:\n"
    ++ M.ppEvent mev
eventsEq _ (lev:_) (mev:_) = do
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

stateEq :: IsSymExprBuilder sym
        => sym
        -> L.LState
        -> M.MState sym ids
        -> VCGMonad sym ids ()
stateEq sym lstate mstate = do
  -- Check event traces equality
  let levs = reverse $ L.events lstate
  let mevs = reverse $ M.events mstate
  eventsEq sym levs mevs

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

runVCG :: VCGConfig sym ids -> VCGMonad sym ids () -> IO (PfState sym)
runVCG cfg action =
  let s = PfState { pfCmds = []
                  , preConds = []
                  , goals = []
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


  Some gen <- newIONonceGenerator
  sym <- newSimpleBackend gen

  let mkLLVMDecl :: Typed Ident -> SMT.Command
      mkLLVMDecl (Typed (PrimType (Integer 64)) (Ident arg)) =
        let vnm = "llvmarg_" <> Text.pack arg
         in SMT.declareFun vnm [] (SMT.bvType 64)
      mkLLVMDecl  (Typed tp _) =
        error $ "Unexpected type " ++ show tp

  let llvmArgDecls = mkLLVMDecl <$> defArgs lFun

  let mkLLVMArg :: Typed Ident -> SMT.Term
      mkLLVMArg (Typed _ (Ident arg)) = L.smtVar ("llvmarg_" <> Text.pack arg)


  let llvmVals :: [SMT.Term]
      llvmVals     = mkLLVMArg <$> defArgs lFun

  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."

  Some stGen <- liftIO $ stToIO $ newSTNonceGenerator

  let ls0 = L.inject $ zip (typedValue <$> defArgs lFun) llvmVals
  ms0 <- M.inject sym


  let vcgCfg =  VCGConfig { blockMapping = Map.empty
                          , llvmMod = lMod
                          , exprBuilder = sym
                          , symIsBuilder = \x -> x
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
  pfSt <- runVCG vcgCfg $ stateEq sym ls' ms'

  -- write proof to smt file
  putStrLn $ "Writing SMT formulas to " ++ outDir
  let Just lbl = bbLabel firstBlock
  forM_ (zip [0..] (goals pfSt)) $ \(i, (goal_lval, goal_mval)) -> do
    let fname = llvmFunName vfi ++ "_" ++ ppBlock lbl ++ "_" ++ show (i::Integer) ++ ".smt"
    bracket (openFile (outDir </> fname) ReadWriteMode) hClose $ \h -> do
      writeCommand h $ SMT.setLogic SMT.allSupported
      writeCommand h $ SMT.setOption (SMT.produceModels True)

      -- Generate LLVM arguments
      mapM_ (writeCommand h) llvmArgDecls

      bindings <- getSymbolVarBimap sym
      c <- SMT2.newWriter CVC4 h "CVC4" True cvc4Features True bindings

      let assertEq lv reg = do
            let M.MSymExpr mval = M.initRegs ms0^.boundValue reg
            mv <- SMT2.mkSMTTerm c mval
            writeCommand h $ SMT.assert $ SMT.eq [lv, mv]
      zipWithM_ assertEq llvmVals x86ArgRegs

      -- Write commands from proof state
      mapM_ (writeCommand h) (reverse (pfCmds pfSt))

      forM_ (preConds pfSt) $ \(lv, mval) -> do
        mv <- SMT2.mkSMTTerm c mval
        writeCommand h $ SMT.assert $ SMT.eq [lv, mv]
      do mv <- SMT2.mkSMTTerm c goal_mval
         writeCommand h $ SMT.assert $ SMT.distinct [goal_lval, mv]
      writeCommand h SMT.checkSat
      writeCommand h SMT.exit

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
