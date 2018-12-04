{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module VCGMacaw
  ( declRegs
  , smtRegVar
  , blockEvents
  , Event(..)
  , ppEvent
  , memVar
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Macaw.CFG as M
import           Data.Macaw.CFG.Block
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
import           Data.Word
import           GHC.Stack
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import           VCGCommon

memVar :: Integer -> Var
memVar i = "x86mem_" <> Text.pack (show i)

smtRegVar :: X86Reg tp -> Text
smtRegVar reg = "x86reg_" <> Text.pack (show reg)

smtLocalVar :: AssignId ids tp -> Text
smtLocalVar (AssignId n) = "x86local_" <> Text.pack (show (indexValue n))

macawError :: HasCallStack => String -> a
macawError msg = error $ "[Macaw Error] " ++ msg

initReg :: X86Reg tp
        -> Const SMT.Term tp
initReg reg = Const $ varTerm (smtRegVar reg)

evalMemAddr :: Map RegionIndex SMT.Term
            -> MemAddr 64
            -> SMT.Term
evalMemAddr m a =
  case Map.lookup (addrBase a) m of
    Nothing -> error "evalMemAddr given address with bad region index."
    Just b -> SMT.bvadd b [SMT.bvdecimal (toInteger (addrOffset a)) 64]

data Event
  = CmdEvent !SMT.Command
  | InstructionEvent !(MemSegmentOff 64)
    -- ^ Marker to indicate the instruction at the given address will be executed.
  | ReadEvent !SMT.Term !Integer !Var
    -- ^ `ReadEvent a w v` indicates that we read `w` bytes from `a`,
    -- and assign the value returned to `v`.
  | CondReadEvent !SMT.Term !SMT.Term !Integer !SMT.Term !Var
    -- ^ `CondReadEvent c a w d v` indicates that we read `w` bytes from `a` when
    -- condition `c` holds, and assign the return value to `v`.   When `c`
    -- is false, then assign `d` to `v`.
  | WriteEvent !SMT.Term !Integer !SMT.Term
    -- ^ `WriteEvent a w v` indicates that we write the `w` byte value `v`  to `a`.
    --
    -- This has side effects, so we record the event.
  | FetchAndExecuteEvent !(RegState (ArchReg X86_64) (Const SMT.Term))

  | BranchEvent !SMT.Term
                !(RegState (ArchReg X86_64) (Const SMT.Term))
                !(RegState (ArchReg X86_64) (Const SMT.Term))

ppEvent :: Event
        -> String
ppEvent (InstructionEvent _) = "instruction"
ppEvent CmdEvent{} = "cmd"
ppEvent ReadEvent{} = "read"
ppEvent CondReadEvent{} = "condRead"
ppEvent WriteEvent{} = "write"
ppEvent (FetchAndExecuteEvent _) = "fetchAndExecute"
ppEvent (BranchEvent _ _ _) = "branch"

instance Show Event where
  show = ppEvent

data MState = MState
  { blockStartAddr :: !(MemSegmentOff 64)
    -- ^ Initial address of block.
  , locals   :: !(Map Word64 SMT.Term)
    -- ^ Map from local indices to associated term.
  , initRegs :: !(RegState X86Reg (Const SMT.Term))
  , events   :: [Event]
  }

initRegDecl :: X86Reg tp
            -> SMT.Command
initRegDecl reg = SMT.declareFun (smtRegVar reg) [] (toSMTType (M.typeRepr reg))

------------------------------------------------------------------------
-- MStateM

type MStateM a = StateT MState IO a

addEvent :: Event -> MStateM ()
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

toSMTType :: M.TypeRepr tp -> SMT.Sort
toSMTType (M.BVTypeRepr w) = SMT.bvSort (natValue w)
toSMTType M.BoolTypeRepr = SMT.boolSort
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
    SExt x w -> do
      xv <- primEval x
      -- This sign extends x
      doSet $ SMT.bvsignExtend (natValue w-natValue (M.typeWidth x)) xv
    UExt x w -> do
      xv <- primEval x
      -- This sign extends x
      doSet $ SMT.bvzeroExtend (natValue w-natValue (M.typeWidth x)) xv
    UadcOverflows x y c -> do
      -- We check for unsigned overflow by zero-extending x, y, and c, performing the
      -- addition, and seeing if the most signicant bit is non-zero.
      xv <- primEval x
      yv <- primEval y
      cv <- primEval c
      let w :: Integer
          w = natValue (M.typeWidth x)
      -- Do zero extensions
      let xext = SMT.bvzeroExtend 1 xv
      let yext = SMT.bvzeroExtend 1 yv
      let cext = SMT.bvzeroExtend w (SMT.ite cv SMT.bit1 SMT.bit0)
      -- Perform addition
      let rext = SMT.bvadd xext [yext, cext]
      -- Unsigned overflow occurs if most-significant bit is set.
      doSet $ SMT.eq [SMT.extract w w rext, SMT.bit1]
    SadcOverflows x y c -> do
      -- We check for signed overflow by adding x, y, and c, checking two things:
      -- x & y have the same sign, and c has t

      -- addition, and seeing if the most signicant bit is non-zero.
      xv <- primEval x
      yv <- primEval y
      cv <- primEval c
      let w :: Integer
          w = natValue (M.typeWidth x)
      -- Carry is positive.
      let cext = SMT.bvzeroExtend (w-1) (SMT.ite cv SMT.bit1 SMT.bit0)
      -- Perform addition
      let r = SMT.bvadd xv [yv, cext]
      -- Check sign property.
      let xmsb = SMT.extract (w-1) (w-1) xv
      let ymsb = SMT.extract (w-1) (w-1) yv
      let rmsb = SMT.extract (w-1) (w-1) r

      doSet $ SMT.and [SMT.eq [xmsb, ymsb], SMT.distinct [xmsb, rmsb]]

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
      addEvent $ ReadEvent addrTerm (natValue w) valVar

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
      addEvent $ CondReadEvent condTerm addrTerm (natValue w) defTerm valVar

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
    InstructionStart off _mnem -> do
      blockAddr <- gets blockStartAddr
      let Just addr = incSegmentOff blockAddr (toInteger off)
      addEvent $ InstructionEvent addr
    Comment _s -> return ()                 -- NoOps
    ArchState _a _m -> return ()             -- NoOps
    ExecArchStmt{} -> error "stmt2SMT unsupported statement."

{-
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
-}

termStmt2SMT :: TermStmt X86_64 ids
             -> MStateM ()
termStmt2SMT tstmt =
  case tstmt of
    FetchAndExecute st -> do
      regs <- traverseF evalToMSymExpr st
      addEvent $ FetchAndExecuteEvent regs
    Branch{} ->
      error "Unexpected branch"
    TranslateError _regs msg ->
      error $ "TranslateError : " ++ Text.unpack msg
    ArchTermStmt stmt _regs ->
      error $ "Unsupported : " ++ show (prettyF stmt)

block2SMT :: Block X86_64 ids
          -> MStateM ()
block2SMT b = do
  mapM_ stmt2SMT (blockStmts b)
  termStmt2SMT (blockTerm b)

declRegs :: [SMT.Command]
declRegs = (\(Some r) -> initRegDecl r) <$> archRegs

blockEvents :: MemSegmentOff 64 -> Word64 -> IO [Event]
blockEvents addr sz = do
  Some stGen <- stToIO $ newSTNonceGenerator
  let loc = rootLoc addr
  mBlock <- stToIO $ disassembleFixedBlock stGen loc (fromIntegral sz)
  case mBlock of
    Left err -> error $ "Translation error: " ++ show err
    Right b -> do
      let regs = mkRegState initReg
      let ms0 = MState { blockStartAddr = addr
                       , locals = Map.empty
                       , initRegs = regs
                       , events = []
                       }
      ms <- execStateT (block2SMT b) ms0
      pure $ reverse $ events ms
