import Galois.Data.ByteArray
import LeanLLVM.AST
import LeanLLVM.PP
import ReoptVCG.Elf
import ReoptVCG.Annotations
import ReoptVCG.VCGBackend
import ReoptVCG.MCStdLib

import SMTLIB.Syntax
import DecodeX86.DecodeX86

-- TODO move these (or similar fns) to lean-llvm
def LLVM.Ident.pp : LLVM.Ident → String := LLVM.Doc.render ∘ LLVM.HasPP.pp
def LLVM.LLVMType.pp : LLVM.LLVMType → String := LLVM.Doc.render ∘ LLVM.HasPP.pp
def LLVM.BlockLabel.pp : LLVM.BlockLabel → String := LLVM.Doc.render ∘ LLVM.HasPP.pp

namespace LLVM

namespace BlockLabel

def lt : forall (x y : BlockLabel), Prop
  | { label := x }, {label := y } => x < y

instance : HasLess BlockLabel := ⟨lt⟩
 
instance decideableBlockLabelLt : ∀(x y:BlockLabel), Decidable (x < y)
| { label := x }, { label := y } =>
  (match Ident.decideLt x y with
   | Decidable.isTrue  p => Decidable.isTrue p
   | Decidable.isFalse p => Decidable.isFalse p
   )

end BlockLabel
end LLVM

namespace ReoptVCG

-- FIXME double check on which interface/API/etc to use here =\
-- The SMT.Raw namespace feels like it has the direct equivalents
-- to the What4.Protocol.SMTLib2.Syntax module in Haskell, but...
-- it's the "Raw" interface which feels a little off...

open SMT


@[reducible]
def FnName := String


inductive VerificationMode
| defaultMode : VerificationMode
| exportMode : String → VerificationMode
| runSolverMode : String → List String → VerificationMode

def VerificationMode.isDefault : VerificationMode → Bool
| VerificationMode.defaultMode => true
| _ => false


-- Like VCGArgs in Main but with all mandatory fields no longer as Options.
structure VCGConfig :=
(annFile : String)
(mode : VerificationMode)
(verbose : Bool)

-- TODO / FIXME see comment below about moving away from IO          
-- FIXME(AMK) don't use the raw interface to SMT?
structure ProverInterface :=
(addSMTCallback     : SMT.smtM Unit → IO Unit)
(addCommandCallback : command → IO Unit)
(proveFalseCallback : term sort.smt_bool → String → IO Unit)
(proveTrueCallback  : term sort.smt_bool → String → IO Unit)
(blockErrorCallback : Nat → Nat → String → IO Unit) -- what do we do there? Do nothing for now...?

namespace ProverInterface

open SMT (smtM)

def runsmtM {a : Type} (p : ProverInterface) (idGen : IdGen) (m : smtM a) : IO (a × IdGen) :=
  match SMT.runsmtM idGen m with
  | (r, (idGen', cmds)) => do
    _ <- List.mapM p.addCommandCallback cmds;
    pure (r, idGen')
  
end ProverInterface

structure ProverSessionGenerator :=
(blockCallback : FnName → LLVM.BlockLabel → (ProverInterface → IO Unit) → IO Unit)
(sessionComplete : IO UInt32)

@[reducible]
def LLVMTypeMap := Std.RBMap String (Option LLVM.LLVMType) Lean.strLt


structure ModuleVCGContext :=
(annotations : ModuleAnnotations)
-- ^ Annotations for module.
(decoder : decodex86.decoder )
-- ^ Machine code memory / decoder state
(symbolAddrMap : Std.RBMap String (elf.word elf.elf_class.ELF64) Lean.strLt)
-- ^ Maps bytes to the symbol name
(writeStderr : Bool)
-- ^ Controls whether logs, warnings or errors
-- chould be written to stderr.
--
-- If false, the messages are droped, but warning
-- count is increased.
(errorCount : IO.Ref Nat)
-- ^ Counts numbers of warnings generated during
-- verification for display at end of run.
(proverGen : ProverSessionGenerator)
-- ^ Interface for generating prover sessions.
(moduleTypeMap : LLVMTypeMap)
-- ^ type map for module.


-------------------------------------------------------
-- Error/Exception Data
-------------------------------------------------------


/-- Errors that are tied to a specific function. --/
inductive FnError
| notFound : FnError
| argTypeUnsupported : LLVM.Ident -> LLVM.LLVMType -> FnError
| missingEntryBlock : FnError
| entryUnreachable : FnError 
| custom : String -> FnError


namespace FnError

--instance : HasCoe String FnError := ⟨FnError.custom⟩

def pp : FnError → String
| notFound => "Could not find definition in LLVM."
| argTypeUnsupported x t => 
  "Function argument "++x.pp++"has unsupported type "++t.pp++"."
| missingEntryBlock => "Function body is missing an entry block."
| entryUnreachable => "Function entry marked unreachable."
| custom msg  => msg

instance : HasToString FnError := ⟨pp⟩

end FnError


inductive BlockError
| annParseFailure : String → BlockError
| missingAnnotations : BlockError
| unsupportedPhiVarType : LLVM.Ident → LLVM.LLVMType → BlockError
| blockAddrInvalid : elf.word elf.elf_class.ELF64 → BlockError

namespace BlockError

def pp : BlockError → String
| annParseFailure msg => "Annotation parse failure: " ++ msg
| missingAnnotations => "Could not find block annotations."
| unsupportedPhiVarType x t => 
  "Phi variable "++x.pp++" has unsupported type "++t.pp++"."
| blockAddrInvalid addr => 
  "Annotated block address "++addr.pp_hex++" is not not in code segment."

end BlockError


inductive ModuleError
| custom : String → ModuleError
| function : FnName → FnError → ModuleError
| block : FnName → LLVM.BlockLabel → BlockError → ModuleError
| io : IO.Error -> ModuleError

namespace ModuleError

def pp : ModuleError → String
| custom msg => msg
| function fnm ferr => fnm++". "++ferr.pp
| block fnm lbl err => fnm++"."++lbl.pp++". "++err.pp
| io err => err.toString

def toIOError : ModuleError → IO.Error
| io ioErr => ioErr
| e => IO.userError $ "Uncaught module VCG error: " ++ e.pp


-- instance HasExceptModuleError : MonadExcept ModuleError (EIO ModuleError) :=
-- inferInstanceAs (MonadExcept ModuleError (EIO ModuleError))

-- def liftIO {α} (m : EIO IO.Error α) : EIO ModuleError α := 
--   m.adaptExcept io

-- instance : HasMonadLiftT IO (EIO ModuleError) := {monadLift := @ModuleError.liftIO}

-- def throwIO {α} (err : IO.Error) : EIO ModuleError α := throw $ ModuleError.io err
-- def catchIO {α} (m : EIO ModuleError α) (h : IO.Error → EIO ModuleError α) : EIO ModuleError α := 
-- let handler : ModuleError → EIO ModuleError α := 
--   λ e => match e with
--          | ModuleError.io e => h e
--          | _ => throw e;
-- catch m handler

-- instance HasExceptIO : MonadExcept IO.Error (EIO ModuleError) :=
--   {throw := @ModuleError.throwIO,
--    catch := @ModuleError.catchIO }

end ModuleError


-------------------------------------------------------
-- ModuleVCG (monad and some basic helpers)
-------------------------------------------------------


-- A monad for running verification of an entire module
-- TODO / FIXME we'll want to move away from EIO at, see
-- https://github.com/GaloisInc/reopt-vcg/pull/53#discussion_r408440682 
@[reducible]
def ModuleVCG := ReaderT ModuleVCGContext IO

namespace ModuleVCG

instance : Functor ModuleVCG := 
  inferInstanceAs (Functor (ReaderT ModuleVCGContext IO))
instance : Applicative ModuleVCG :=
  inferInstanceAs (Applicative (ReaderT ModuleVCGContext IO))
instance : Monad ModuleVCG :=
  inferInstanceAs (Monad (ReaderT ModuleVCGContext IO))

-- Run "standard" IO by wrapping any exceptions thrown in our Module.Error.IO wrapper.
-- def liftIO {α} (m : IO α) : ModuleVCG α := 
--   monadLift $ m.adaptExcept ModuleError.io

-- instance : HasMonadLiftT IO ModuleVCG := {monadLift := @ModuleVCG.liftIO}
instance : MonadReader ModuleVCGContext ModuleVCG :=
  inferInstanceAs (MonadReader ModuleVCGContext (ReaderT ModuleVCGContext IO))

-- def throwIO {α} (err : IO.Error) : ModuleVCG α := throw $ ModuleError.io err
-- def catchIO {α} (m : ModuleVCG α) (h : IO.Error → ModuleVCG α) : ModuleVCG α := 
-- let handler : ModuleError → ModuleVCG α := 
--   λ e => match e with
--          | ModuleError.io e => h e
--          | _ => throw e;
-- catch m handler

-- instance : MonadExcept IO.Error ModuleVCG :=
--   {throw := @ModuleVCG.throwIO,
--    catch := @ModuleVCG.catchIO }


-- instance : MonadIO ModuleVCG :=
--   {throw := @ModuleVCG.throwIO,
--    catch := @ModuleVCG.catchIO,
--    monadLift := @ModuleVCG.liftIO}

instance : MonadIO ModuleVCG :=
inferInstanceAs (MonadIO (ReaderT ModuleVCGContext IO))

end ModuleVCG


def runModuleVCG (ctx : ModuleVCGContext) (m : ModuleVCG Unit) : IO Unit := m.run ctx

def vcgLog (msg : String) : ModuleVCG Unit := do 
  ctx ← read;
  when ctx.writeStderr $ 
    IO.println msg -- FIXME can't find the handle for stderr =\

-- A warning that stops execution until catch.
def functionError {α} (fnm : FnName) (e : FnError) : ModuleVCG α :=
throw $ IO.userError $ ModuleError.pp $ ModuleError.function fnm e

-- A warning that stops execution until catch.
def blockError {α} (fnm : FnName) (lbl : LLVM.BlockLabel) (e : BlockError) : ModuleVCG α :=
  throw $ IO.userError $ ModuleError.pp $ ModuleError.block fnm lbl e

-- A warning that stops execution until catch.
def moduleThrow {α} (errMsg : String) : ModuleVCG α :=
  throw $ IO.userError $ ModuleError.pp $ ModuleError.custom errMsg


-- Catch a VCG error, print it to the screen and keep going.
def moduleCatch (m : ModuleVCG Unit) :  ModuleVCG Unit :=
  λ (ctx : ModuleVCGContext) =>
    catch (m.run ctx) $ λ (e : IO.Error) => 
      match e with
      | IO.Error.userError msg => do
        when ctx.writeStderr $
          IO.println $ "Error: " ++ msg; -- FIXME use stderr or similar?
        ctx.errorCount.modify (λ n => n + 1)
      | _ => throw e



-------------------------------------------------------
-- Annotated Block
-------------------------------------------------------

@[reducible]
def BlockLabelValMap := Std.RBMap LLVM.BlockLabel LLVM.Value (λ x y => x < y)

abbrev PhiVarMap := Std.RBMap LLVM.Ident (LLVM.LLVMType × BlockLabelValMap) (λ x y => x<y)

structure AnnotatedBlock :=
(annotation: BlockAnn)
(label : LLVM.BlockLabel)
(phiVarMap : PhiVarMap)
(stmts : List LLVM.Stmt)


/--  Maps LLM block labels to their associated annotations. --/
@[reducible]
def ReachableBlockAnnMap := Std.RBMap LLVM.BlockLabel AnnotatedBlock (λ x y => x<y)

-- | Find a block with the given label in the config.
def findBlock (m : ReachableBlockAnnMap) (lbl: LLVM.BlockLabel) : Option (BlockAnn × PhiVarMap) := do
ab <- m.find? lbl;
pure (ab.annotation, ab.phiVarMap)

-------------------------------------------------------
-- BlockVCG
-------------------------------------------------------

abbrev MemAddr := Nat
abbrev MCBlockAnnMap := Std.RBMap MemAddr MemoryAnn (λ x y => x < y)

-- Information that does not change during execution of a BlockVCG action.
structure BlockVCGContext :=
(mcModuleVCGContext : ModuleVCGContext)
  -- ^ Information at module level about CFG.
(llvmFunName : String)
  -- ^ Annotations for the current function.
(funBlkAnnotations : ReachableBlockAnnMap)
  -- ^ Annotations for blocks in the CFG.
(firstBlockLabel : LLVM.BlockLabel)
  -- ^ Label for first block in this function
(currentBlock : LLVM.BlockLabel)
  -- ^ Label for block we are verifying.
(callbackFns : ProverInterface)
  -- ^ Functions for interacting with SMT solver.
(mcBlockEndAddr : MemAddr)
  -- ^ The end address of the block.
(mcBlockMap : MCBlockAnnMap)
  -- ^ Map from addresses to annotations of events on that address.
(mcStdLib     : x86.vcg.MCStdLib)

-- State that changes during execution of a BlockVCG action.
structure BlockVCGState :=
(mcCurAddr : MemAddr)
  -- ^ Address of the current instruction
(mcCurSize : Nat)
  -- ^ Size of current instruction.
--(mcX87Top : Nat) -- TODO...? later
  -- ^ Top index in x86 stack (starts at 7 and grows down).
-- (mcDF : Bool) -- FIXME
  -- ^ Direction flag
(mcCurRegs : x86.vcg.RegState)
  -- ^ Map registers to the SMT term.
(mcCurMem : x86.vcg.memory)
  -- ^ Current memory object
(mcEvents : List x86.vcg.Event)
  -- ^ Unprocessed events from last instruction.
(idGen : IdGen)
  -- ^ Used to generate unique/fresh local variables for machine code SMT terms.
-- (mcPendingAllocaOffsetMap : RBMap LocalIdent AllocaAnn (λ x y => x < y)) -- TODO use later
  -- ^ This is a map from allocation names to the annotations about their
  -- size and offset.
(llvmInstIndex : Nat)
  -- ^ Index of next LLVM instruction within block to execute
  -- Used for error reporting
--(activeAllocaSet : RBTree LocalIdent (λ x y => x < y)) -- TODO use later
 -- ^ Set of allocation names that are active.
(llvmIdentMap : Std.RBMap LLVM.Ident (Sigma SMT.term) (fun x y => x < y))
 -- ^ Mapping from llvm ident to their SMT equivalent.


inductive BlockVCGError
| localErr : String → BlockVCGError
-- ^ The was an error processing the current block which,
--   has halted its verification, but it is reasonable to
--   continue on with the next block's verification.
| globalErr : String → BlockVCGError
-- ^ There is a globally fatal error; it is not reasonable to continue
-- verifying blocks.


def BlockVCG := ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))

namespace BlockVCG

instance : Monad BlockVCG :=
  inferInstanceAs (Monad (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))))

instance : MonadReader BlockVCGContext BlockVCG :=
  inferInstanceAs (MonadReader BlockVCGContext (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))))

instance : MonadState BlockVCGState BlockVCG :=
  inferInstanceAs (MonadState BlockVCGState (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))))

instance : MonadExcept BlockVCGError BlockVCG :=
  inferInstanceAs (MonadExcept BlockVCGError (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))))

instance : HasMonadLiftT IO BlockVCG :=
  inferInstanceAs (HasMonadLiftT IO (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT BlockVCGError IO))))


def liftIO {a : Type} (m : IO a) : BlockVCG a := monadLift m

-- | Thow an error to terminate the current block's verification, but continue with
-- other blocks verification.
def localThrow {a} (msg : String) : BlockVCG a := throw $ BlockVCGError.localErr msg

-- | Thow an error to terminate all verification.
def globalThrow {a} (msg : String) : BlockVCG a := throw $ BlockVCGError.globalErr msg


end BlockVCG

-- FIXME: move
/-- Lift an Except to IO, throwing any occurring error with the given prefix at the front of the message. --/
def elseThrowPrefixed {ε α : Type} [HasToString ε] (e : Except ε α) (pfx : String) : IO α :=
match e with
| Except.ok a    => pure a
| Except.error e => throw (IO.userError $ pfx ++ (toString e))



/-- Maps between LLVM argument and machine code name. --/
structure LLVMMCArgBinding :=
(llvmArgName : LLVM.Ident)
(smtSort: SMT.sort)
(register: x86.reg64)


end ReoptVCG
