{- LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module VCGMacaw
  ( functionHasName
  , inject
  , getDiscState
  , block2SMT
--  , getRAXValue
  , MState(..)
  , MSymExpr(..)
  , MEvent(..)
  , ppEvent
  , getFunNameByRIP
  , evalMemAddr
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad (forM_)
import           Control.Monad.State
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.ElfEdit
import           Data.Macaw.CFG as M
import           Data.Macaw.CFG.Block
import           Data.Macaw.Discovery as M
import           Data.Macaw.Memory.ElfLoader
import qualified Data.Macaw.Types as M
import           Data.Macaw.X86
import           GHC.Stack
--import           Data.Macaw.X86.X86Reg
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Context hiding (null)
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import qualified Data.Text as Text
import           Data.Word
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import qualified What4.BaseTypes as W
import           What4.Interface as W

import           VCGCommon

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

type family ToWhat4Type (tp::M.Type) :: W.BaseType where
  ToWhat4Type M.BoolType = W.BaseBoolType
  ToWhat4Type (M.BVType w) = W.BaseBVType w

-- | A wrapper to represent what4 expression using Macaw types
data MSymExpr sym (tp::M.Type) = MSymExpr (SymExpr sym (ToWhat4Type tp))

evalToMSymExpr :: Value X86_64 ids tp -> MStateM sym ids (MSymExpr sym tp)
evalToMSymExpr v = MSymExpr <$> primEval v

data MEvent sym
  = FetchAndExecuteEvent !(RegState (ArchReg X86_64) (MSymExpr sym))

  | BranchEvent !(SymExpr sym W.BaseBoolType)
                !(RegState (ArchReg X86_64) (MSymExpr sym))
                !(RegState (ArchReg X86_64) (MSymExpr sym))


ppEvent :: MEvent sym
        -> String
ppEvent (FetchAndExecuteEvent _) = "fetchAndExecute"
ppEvent (BranchEvent _ _ _) = "branch"

-- Currently not being used
--newtype Regs' sym b = Regs { getRegMaps :: Map.Map String b }
--type Regs sym = Regs' sym (SymBV64 sym)


freshMacawVariable :: (HasCallStack, IsSymExprBuilder sym)
                   => sym
                   -> SolverSymbol
                   -> M.TypeRepr tp
                   -> IO (SymExpr sym (ToWhat4Type tp))
freshMacawVariable sym nm tp =
  case tp of
    M.BoolTypeRepr -> freshConstant sym nm W.BaseBoolRepr
    M.BVTypeRepr w -> freshConstant sym nm (W.BaseBVRepr w)
    M.TupleTypeRepr _ -> error "Do not support symbolic register types."
    M.FloatTypeRepr _ -> error "Do not support floating point register types."

freshReg :: (HasCallStack, IsSymExprBuilder sym)
         => sym
         -> X86Reg tp
         -> IO (MSymExpr sym tp)
freshReg sym reg = do
  case userSymbol ("reg_" ++ show reg) of
    Left msg -> error $ "freshReg " ++ show reg ++ ": " ++ show msg
    Right nm -> MSymExpr <$> freshMacawVariable sym nm (M.typeRepr reg)


data MState sym ids = MState
  { mstateSym  :: !sym
  , symIsBuilder :: !(forall a . (IsSymExprBuilder sym => a) -> a)
  , locals   :: !(MapF (Nonce ids) (MSymExpr sym))
  , initRegs :: !(RegState X86Reg (MSymExpr sym))
  , curMem      :: !(SymMemory sym)
--  , disjoint :: [Ptr sym]
  , retval   :: Maybe (RegState (ArchReg X86_64) (Value X86_64 ids))
  , events   :: [MEvent sym]
  }

type MStateM sym ids a = StateT (MState sym ids) IO a

io :: (IsSymExprBuilder sym => IO a) -> MStateM sym ids a
io m = do
  f <- gets symIsBuilder
  liftIO $ f m

{-
localsUpdate :: IsSymExprBuilder sym
             => Nonce ids tp
             -> SymExpr sym (ToWhat4Type tp)
             -> MStateM sym ids ()
localsUpdate key val =
  modify $ \s -> s { locals = MapF.insert key (MSymExpr val) (locals s) }
-}

-- Inject initial (symbolic) arguments
-- The [String] are arugment name used for this function
inject :: IsSymExprBuilder sym => sym -> IO (MState sym ids)
inject sym = do
  bv_all0 <- bvLit sym knownNat 0
  mem0 <- constantArray sym (singleton bv64) bv_all0
  regs <- mkRegStateM $ freshReg sym

  pure $! MState { mstateSym = sym
                 , symIsBuilder = \x -> x
                 , locals = MapF.empty
                 , initRegs = regs
                 , curMem = mem0
--                 , disjoint = []
                 , retval = Nothing
                 , events = []
                 }

addEvent :: MEvent sym -> MStateM sym ids ()
addEvent e = modify $ \s -> s { events = e : events s}

readMem :: Ptr sym
        -> M.MemRepr tp
        -> MStateM sym ids (SymExpr sym (ToWhat4Type tp))
readMem ptr (BVMemRepr w _end) = do
  sym <- gets mstateSym
  mem <- gets curMem
  let n = natMultiply (knownNat @8) w
  Just LeqProof <- pure $ testLeq (knownNat @1) n
  io $ readMemBVLE sym mem ptr w
--  s <- get
--  io $ arrayLookup sym (curMem s) (singleton ptr)
--  error "readMem undefined"

writeMem :: Ptr sym
          -> M.MemRepr tp
          -> SymExpr sym (ToWhat4Type tp)
          -> MStateM sym ids ()
writeMem ptr (BVMemRepr _w _end) val = do
  sym <- gets mstateSym
  mem <- gets curMem
  newmem <- io $ writeMemBVLE sym mem ptr val
  modify' $ \s -> s { curMem = newmem }

{-
retValUpdate :: IsSymExprBuilder sym
             => (RegState (ArchReg X86_64) (Value X86_64 ids)) -> MStateM sym ids ()
retValUpdate val = modify $ \s ->
  case retval s of
    Nothing -> s { retval = Just val }
    _ -> macawError "Trying to overwrite an existing return value"
-}

{-
addDisjointPtr :: IsSymExprBuilder sym => (Ptr sym) -> MStateM sym ids ()
addDisjointPtr ptr = modify $ \s -> s { disjoint = ptr:disjoint s }
-}

evalMemAddr :: IsExprBuilder sym
            => sym
            -> Map RegionIndex (SymExpr sym (BaseBVType 64))
            -> MemAddr 64
            -> IO (SymExpr sym (BaseBVType 64))
evalMemAddr sym m a =
  case Map.lookup (addrBase a) m of
    Nothing -> error "evalMemAddr given address with bad region index."
    Just b -> do
      o <- bvLit sym knownNat (toInteger (addrOffset a))
      bvAdd sym b o

primEval :: Value X86_64 ids tp
         -> MStateM sym ids (SymExpr sym (ToWhat4Type tp))
primEval (BVValue w i) = do
  sym <- gets mstateSym
  io $ bvLit sym w i

primEval (BoolValue b) = do
  f <- gets symIsBuilder
  sym <- gets mstateSym
  pure $ f (backendPred sym b)

primEval (AssignedValue (Assignment (AssignId ident) _rhs)) = do
  m <- locals <$> get
  case MapF.lookup ident m of
    Just (MSymExpr v) -> return v
    Nothing -> macawError $ "Not contained in the locals: " ++ show ident

primEval (Initial reg) = do
  regs <- initRegs <$> get
  case regs^.boundValue reg of
    MSymExpr e -> pure e

primEval (RelocatableValue _w addr) = do
  sym <- gets mstateSym
  let m = error "region index map not defined."
  io $ evalMemAddr sym m addr

primEval (SymbolValue _w _id) = do
  macawError "SymbolValue: Not implemented yet"

evalApp2SMT :: App (Value X86_64 ids) tp
            -> MStateM sym ids (SymExpr sym (ToWhat4Type tp))
evalApp2SMT a = do
  sym <- gets mstateSym
  case a of
    BVAdd _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      io $ bvAdd sym xv yv
    BVSub _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      io $ bvSub sym xv yv
    BVMul _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      io $ bvMul sym xv yv
    BVUnsignedLe x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ bvUle sym xv yv
    BVUnsignedLt x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ bvUlt sym xv yv
    BVSignedLe x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ bvSle sym xv yv
    BVSignedLt x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ bvSlt sym xv yv
    Eq x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ isEq sym xv yv
    OrApp x y -> do
      xv <- primEval x
      yv <- primEval y
      io $ orPred sym xv yv
    Trunc x w -> do
      xv <- primEval x
      -- Given the assumption that all data are 64bv, treat it as no ops for the moment.
      io $ bvTrunc sym w xv
    _app -> do
      io $ do
        hPutStrLn stderr $ show (ppApp (\_ -> text "*") a) ++ ": Not implemented yet"
        freshMacawVariable sym emptySymbol (M.typeRepr a)

assignRhs2SMT :: AssignRhs X86_64 (Value X86_64 ids) tp
              -> MStateM sym ids (SymExpr sym (ToWhat4Type tp))
assignRhs2SMT rhs = do
  sym <- gets mstateSym
  case rhs of
    EvalApp a -> do
      evalApp2SMT a

    ReadMem addr mrepr -> do
      -- TODO: dealing with memory representation
      addrv <- primEval addr
      readMem addrv mrepr

    CondReadMem _repr _c _a _d -> do
      error $ "CondReadMem is not implemented yet."

    SetUndefined tp -> do
      io $ freshMacawVariable sym emptySymbol tp

    EvalArchFn _f tp -> do
      io $ do
        hPutStrLn stderr $ "EvalArchFn is not implemented yet."
        freshMacawVariable sym emptySymbol tp

stmt2SMT :: Stmt X86_64 ids -> MStateM sym ids ()
stmt2SMT stmt =
  case stmt of
    AssignStmt (Assignment (AssignId ident) rhs) -> do
      rhsv <- assignRhs2SMT rhs
      modify $ \s -> s { locals = MapF.insert ident (MSymExpr rhsv) (locals s) }
    WriteMem addr repr rhs -> do
      -- TODO: dealing with memory representation
      addrv <- primEval addr
      val   <- primEval rhs
      writeMem addrv repr val
    InstructionStart _off _mnem -> return () -- NoOps
    Comment _s -> return ()                 -- NoOps
    ArchState _a _m -> return ()             -- NoOps
    ExecArchStmt{} -> error "stmt2SMT unsupported statement."

-- | Attempt to interpret the statement list as just a jump to the given address with
-- the registers provided.
blockAsJump :: forall sym ids
            .  Map Word64 (Block X86_64 ids)
            -> Word64
            -> MStateM sym ids (RegState (ArchReg X86_64) (MSymExpr sym))
blockAsJump blockMap off =
  case Map.lookup off blockMap of
    Nothing -> do
      error $ "Can not find block offset " ++ show off
    Just b -> do
      unless (null (blockStmts b)) $ do
        error $ "Branch doesn't support other nonterminal statements."
      case blockTerm b of
        FetchAndExecute s -> do
          traverseF evalToMSymExpr s
        s -> error $ "Unsupported branch terminal: " ++ show (pretty s)

termStmt2SMT :: Map Word64 (Block X86_64 ids)
             -> TermStmt X86_64 ids
             -> MStateM sym ids ()
termStmt2SMT blockMap tstmt =
  case tstmt of
    FetchAndExecute st -> do
      regs <- traverseF evalToMSymExpr st
      addEvent $ FetchAndExecuteEvent regs
    Branch cnd thn els -> do
      cndv <- primEval cnd
      t <- blockAsJump blockMap thn
      f <- blockAsJump blockMap els
      addEvent $ BranchEvent cndv t f
    TranslateError _regs msg ->
      error $ "TranslateError : " ++ Text.unpack msg
    ArchTermStmt stmt _regs ->
      error $ "Unsupported : " ++ show (prettyF stmt)

{-
brTargets :: ParsedTermStmt X86_64 ids -> [ArchSegmentOff X86_64]
brTargets tstmt = case tstmt of
  ParsedCall _st (Just addr) -> [addr]
  ParsedJump _ addr -> [addr]
  ParsedIte _cnd thn els ->
    (brTargets $ stmtsTerm thn) ++ (brTargets $ stmtsTerm els)
  _ -> []
-}

{-
printBlock :: ParsedBlock X86_64 ids -> IO ()
printBlock b = do
  putStrLn $ "Block start: " ++ show (pblockAddr b)
  putStrLn $ "Non terms: "
  forM_ (stmtsNonterm $ blockStatementList b) $ \s ->
    putStrLn $ ("  " ++ show s)
  putStrLn $ "  Terminal: " ++ (show $ stmtsTerm (blockStatementList b))
-}

block2SMT :: Map Word64 (Block X86_64 ids)
          -> Block X86_64 ids
          -> MStateM sym ids ()
block2SMT blockMap b = do
--  io $ printBlock b
  mapM_ stmt2SMT (blockStmts b)
  termStmt2SMT blockMap (blockTerm b)

getFunNameByRIP :: DiscoveryState X86_64 -> Value X86_64 ids tp -> String
getFunNameByRIP discInfo (RelocatableValue _w addr) =
  case (`Map.lookup` (discInfo^.funInfo)) =<< asSegmentOff (memory discInfo) addr of
    Just (Some f) -> BSC.unpack (discoveredFunName f)
    Nothing -> macawError $ "Can not find Macaw function at " ++ (show addr)
getFunNameByRIP _ _ = macawError "TODO"

functionHasName :: Some (DiscoveryFunInfo X86_64) -> BS.ByteString -> Bool
functionHasName (Some f) name = discoveredFunName f == name

--findBlockByOffset :: DiscoveryFunInfo X86_64 ids -> ArchSegmentOff X86_64 -> ParsedBlock X86_64 ids
--findBlockByOffset f offset = (f^.parsedBlocks) Map.! offset

--getEntryBlock :: DiscoveryFunInfo X86_64 ids -> ParsedBlock X86_64 ids
--getEntryBlock f = findBlockByOffset f (discoveredFunAddr f)

{-
getRAXValue :: W.IsSymExprBuilder sym => sym -> MState sym ids -> IO (Maybe (SymBV64 sym))
getRAXValue sym s =
  error "getRAXValue undefined"
  case retval s of
    Just regs -> do
      Just <$> evalStateT (primEval (regs ^. boundValue RAX)) s
    Nothing ->
      return Nothing
-}

getDiscState :: FilePath -> IO (DiscoveryState X86_64)
getDiscState elfFilePath = do
  e <- readElf elfFilePath
  -- Construct memory representation of Elf file.
  let loadOpts = defaultLoadOptions

  (warnings, mem, _entry, symbols) <- either fail pure $
    resolveElfContents loadOpts e
  forM_ warnings $ \w -> do
    hPutStrLn stderr w

  let ainfo = x86_64_linux_info
  -- Create map from symbol addresses to name.
  let addrSymMap = Map.fromList [ (memSymbolStart msym, memSymbolName msym) | msym <- symbols ]
  -- Create initial discovery state.
  pure $ emptyDiscoveryState mem addrSymMap ainfo

macawError :: HasCallStack => String -> a
macawError msg = error ("[Macaw Error] " ++ msg)

--macawWarning :: String -> IO ()
--macawWarning msg = putStrLn ("[Macaw Warning] " ++ msg)
