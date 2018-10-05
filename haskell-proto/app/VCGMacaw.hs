{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module VCGMacaw
  ( {- functionHasName -}
    inject
  , getDiscState
  , block2SMT
  , MState(..)
  , MEvent(..)
  , ppEvent
  , memVar
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.State
import qualified Data.ByteString as BS
import           Data.ElfEdit
import           Data.Macaw.CFG as M
import           Data.Macaw.CFG.Block
import           Data.Macaw.Discovery as M
import           Data.Macaw.Memory.ElfLoader
import qualified Data.Macaw.Types as M
import           Data.Macaw.X86
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Word
import           GHC.Stack
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import qualified What4.Protocol.SMTLib2.Syntax as SMT

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

memVar :: Integer -> Var
memVar i = "x86mem_" <> Text.pack (show i)

smtRegVar :: X86Reg tp -> Text
smtRegVar reg = "x86reg_" <> Text.pack (show reg)

smtLocalVar :: AssignId ids tp -> Text
smtLocalVar (AssignId n) = "x86local_" <> Text.pack (show (indexValue n))

macawError :: HasCallStack => String -> a
macawError msg = error $ "[Macaw Error] " ++ msg

evalMemAddr :: Map RegionIndex SMT.Term
            -> MemAddr 64
            -> SMT.Term
evalMemAddr m a =
  case Map.lookup (addrBase a) m of
    Nothing -> error "evalMemAddr given address with bad region index."
    Just b -> SMT.bvadd b [SMT.bvdecimal (toInteger (addrOffset a)) 64]

data MEvent
  = CmdEvent !SMT.Command
  | CondReadEvent !SMT.Term !SMT.Term !Integer !Var
    -- ^ `CondReadEvent c a w v` indicates that we read `w` bytes from `a` when
    -- condition `c` holds, and the read returned the value `v`.
    --
    -- This can have a side effect, so we record the event.  When `c` is false,
    -- then the read value `v` is irrelevant.
  | WriteEvent !SMT.Term !Integer !SMT.Term
    -- ^ `WriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.
    --
    -- This has side effects, so we record the event.
  | FetchAndExecuteEvent !(RegState (ArchReg X86_64) (Const SMT.Term))

  | BranchEvent !SMT.Term
                !(RegState (ArchReg X86_64) (Const SMT.Term))
                !(RegState (ArchReg X86_64) (Const SMT.Term))

ppEvent :: MEvent
        -> String
ppEvent CmdEvent{} = "cmd"
ppEvent CondReadEvent{} = "read"
ppEvent WriteEvent{} = "write"
ppEvent (FetchAndExecuteEvent _) = "fetchAndExecute"
ppEvent (BranchEvent _ _ _) = "branch"

data MState = MState
  { locals   :: !(Map Word64 SMT.Term)
  , initRegs :: !(RegState X86Reg (Const SMT.Term))
--  , memIndex  :: !Integer
--  , curMem      :: !SMem
  , retval   :: Maybe (RegState X86Reg (Const SMT.Term))
  , events   :: [MEvent]
  }

initRegDecl :: X86Reg tp
            -> SMT.Command
initRegDecl reg = SMT.declareFun (smtRegVar reg) [] (toSMTType (M.typeRepr reg))

inject :: MState
inject =
  MState { locals = Map.empty
         , initRegs = mkRegState initReg
         --, curMem = SMem (varTerm (memVar 0))
         --, memIndex = 1
         , retval = Nothing
         , events = ((\(Some r) -> CmdEvent (initRegDecl r)) <$> reverse archRegs)
--                 ++ [CmdEvent (SMT.declareFun (memVar 0) [] memType)]
         }

------------------------------------------------------------------------
-- MStateM

type MStateM a = StateT MState IO a

addEvent :: MEvent -> MStateM ()
addEvent e = modify $ \s -> s { events = e : events s}

------------------------------------------------------------------------
-- Translation

primEval :: Value X86_64 ids tp
         -> MStateM SMT.Term
primEval (BVValue w i) = do
  pure $ SMT.bvdecimal i (natValue w)

primEval (BoolValue b) = do
  pure $ if b then SMT.true else SMT.false

primEval (AssignedValue (Assignment (AssignId ident) _rhs)) = do
  m <- locals <$> get
  case Map.lookup (indexValue ident) m of
    Just v -> return v
    Nothing -> macawError $ "Not contained in the locals: " ++ show ident

primEval (Initial reg) = do
  regs <- initRegs <$> get
  case regs^.boundValue reg of
    Const e -> pure e

primEval (RelocatableValue _w addr) = do
  let m = error "region index map not defined."
  pure $ evalMemAddr m addr

primEval (SymbolValue _w _id) = do
  macawError "SymbolValue: Not implemented yet"

evalToMSymExpr :: Value X86_64 ids tp -> MStateM (Const SMT.Term tp)
evalToMSymExpr v = Const <$> primEval v

initReg :: X86Reg tp
         -> Const SMT.Term tp
initReg reg = Const $ varTerm (smtRegVar reg)

toSMTType :: M.TypeRepr tp -> SMT.Type
toSMTType (M.BVTypeRepr w) = SMT.bvType (natValue w)
toSMTType M.BoolTypeRepr = SMT.boolType
toSMTType tp = error $ "toSMTType: unsupported type " ++ show tp

{-
readMem :: SMT.Term
        -> M.MemRepr tp
        -> MStateM SMT.Term
readMem ptr (BVMemRepr w end) = do
  when (end /= LittleEndian) $ do
    error "reopt-vcg only encountered big endian read."
  -- TODO: Add assertion that memory is valid.
  mem <- gets curMem
  pure $ readBVLE mem ptr (natValue w)

writeMem :: SMT.Term
         -> M.MemRepr tp
         -> SMT.Term
         -> MStateM ()
writeMem ptr (BVMemRepr w LittleEndian) val = do
  modify' $ \s ->
    let SMem newMem = writeBVLE (curMem s) ptr val (natValue w)
        cmd = SMT.defineFun (memVar (memIndex s)) [] memType newMem
     in s { curMem = SMem (varTerm (memVar (memIndex s)))
          , memIndex = memIndex s + 1
          , events = CmdEvent cmd : events s
          }
-}

setDefined :: AssignId ids tp
           -> M.TypeRepr tp
           -> SMT.Term
           -> MStateM ()
setDefined (AssignId n) tp t = do
  let nm = smtLocalVar (AssignId n)
  let decl = SMT.defineFun nm [] (toSMTType tp) t
  modify $ \s -> s { events = CmdEvent decl : events s
                   , locals = Map.insert (indexValue n) (varTerm nm) (locals s)
                   }

-- | The the local value to be undefined assign id to be undefined
setUndefined :: AssignId ids tp
             -> MStateM Var
setUndefined (AssignId n) = do
  let nm = smtLocalVar (AssignId n)
  modify $ \s -> s { locals = Map.insert (indexValue n) (varTerm nm) (locals s) }
  pure $! nm

evalApp2SMT :: AssignId ids tp
            -> App (Value X86_64 ids) tp
            -> MStateM ()
evalApp2SMT aid a = do
  let doSet v = do
        setDefined aid (M.typeRepr a) v
  case a of
    BVAdd _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      doSet $ SMT.bvadd xv [yv]
    BVSub _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      doSet $ SMT.bvsub xv yv
    BVMul _w x y -> do
      xv  <- primEval x
      yv  <- primEval y
      doSet $ SMT.bvmul xv [yv]
    BVUnsignedLe x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.bvule xv yv
    BVUnsignedLt x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.bvult xv yv
    BVSignedLe x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.bvsle xv yv
    BVSignedLt x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.bvslt xv yv
    Eq x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.eq [xv,yv]
    OrApp x y -> do
      xv <- primEval x
      yv <- primEval y
      doSet $ SMT.or [xv,yv]
    Trunc x w -> do
      xv <- primEval x
      -- Given the assumption that all data are 64bv, treat it as no ops for the moment.
      doSet $ SMT.extract (natValue w-1) 0 xv
    _app -> do
      liftIO $ hPutStrLn stderr $ show (ppApp (\_ -> text "*") a) ++ ": Not implemented yet"
      var <- setUndefined aid
      addEvent $ CmdEvent $ SMT.declareFun var [] (toSMTType (M.typeRepr a))


assignRhs2SMT :: AssignId ids tp
              -> AssignRhs X86_64 (Value X86_64 ids) tp
              -> MStateM ()
assignRhs2SMT aid rhs = do
  case rhs of
    EvalApp a -> do
      evalApp2SMT aid a

    ReadMem addr (BVMemRepr w end) -> do
      when (end /= LittleEndian) $ do
        error "reopt-vcg only encountered big endian read."
      addrTerm <- primEval addr
      valVar <- setUndefined aid
      -- Add conditional read event.
      addEvent $ CondReadEvent SMT.true addrTerm (natValue w) valVar

    CondReadMem (BVMemRepr w end) cond addr def -> do
      when (end /= LittleEndian) $ do
        error "reopt-vcg only encountered big endian read."
      condTerm <- primEval cond
      addrTerm <- primEval addr
      defTerm <- primEval def

      -- Set location of read to fresh constant.
      valVar <- setUndefined aid

      -- Assert that value = default when cond is false
      -- Add conditional read event.
      addEvent $ CondReadEvent condTerm addrTerm (natValue w) valVar
      addEvent $ CmdEvent $ SMT.assert $
        SMT.or [condTerm, SMT.eq [varTerm valVar, defTerm]]

    SetUndefined tp -> do
      var <- setUndefined aid
      addEvent $ CmdEvent $ SMT.declareFun var [] (toSMTType tp)

    EvalArchFn _f tp -> do
      liftIO $ hPutStrLn stderr $ "EvalArchFn is not implemented yet."
      var <- setUndefined aid
      addEvent $ CmdEvent $ SMT.declareFun var [] (toSMTType tp)

stmt2SMT :: Stmt X86_64 ids -> MStateM ()
stmt2SMT stmt =
  case stmt of
    AssignStmt (Assignment aid rhs) -> do
      assignRhs2SMT aid rhs
    WriteMem addr (BVMemRepr w end) val -> do
      when (end /= LittleEndian) $ do
        error "reopt-vcg only encountered big endian read."
      -- TODO: dealing with memory representation
      addrTerm <- primEval addr
      valTerm  <- primEval val
      addEvent $ WriteEvent addrTerm (natValue w) valTerm
    InstructionStart _off _mnem -> return () -- NoOps
    Comment _s -> return ()                 -- NoOps
    ArchState _a _m -> return ()             -- NoOps
    ExecArchStmt{} -> error "stmt2SMT unsupported statement."

-- | Attempt to interpret the statement list as just a jump to the given address with
-- the registers provided.
blockAsJump :: forall ids
            .  Map Word64 (Block X86_64 ids)
            -> Word64
            -> MStateM (RegState (ArchReg X86_64) (Const SMT.Term))
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
             -> MStateM ()
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

block2SMT :: Map Word64 (Block X86_64 ids)
          -> Block X86_64 ids
          -> MStateM ()
block2SMT blockMap b = do
  mapM_ stmt2SMT (blockStmts b)
  termStmt2SMT blockMap (blockTerm b)

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
