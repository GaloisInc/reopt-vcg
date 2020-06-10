import Galois.Data.ByteArray
import LeanLLVM.AST
import LeanLLVM.PP
import Main.Elf
import ReoptVCG.Annotations
import SMTLIB.Syntax
import DecodeX86.DecodeX86

-- TODO move these (or similar fns) to lean-llvm
def llvm.ident.pp := pp.render ∘ llvm.pp_ident
def llvm.llvm_type.pp := pp.render ∘ llvm.pp_type
def llvm.block_label.pp := pp.render ∘ llvm.pp_label

namespace llvm

namespace block_label

def lt : forall (x y : block_label), Prop
  | { label := x }, {label := y } => x < y

instance : HasLess block_label := ⟨lt⟩
 
instance decideableBlockLabelLt : ∀(x y:block_label), Decidable (x < y)
| { label := x }, { label := y } =>
  (match ident.decideLt x y with
   | Decidable.isTrue  p => Decidable.isTrue p
   | Decidable.isFalse p => Decidable.isFalse p
   )

end block_label
end llvm

namespace ReoptVCG

-- FIXME double check on which interface/API/etc to use here =\
-- The SMTLIB.Raw namespace feels like it has the direct equivalents
-- to the What4.Protocol.SMTLib2.Syntax module in Haskell, but...
-- it's the "Raw" interface which feels a little off...

open SMTLIB.Raw


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
-- FIXME(AMK) don't use the raw interface to SMTLIB
structure ProverInterface :=
(addCommandCallback : command → IO Unit)
(proveFalseCallback : term const_sort.smt_bool → String → IO Unit)
(proveTrueCallback  : term const_sort.smt_bool → String → IO Unit)
(blockErrorCallback : Int → Nat → String → IO Unit)

structure ProverSessionGenerator :=
(blockCallback : FnName → llvm.block_label → (ProverInterface → IO Unit) → IO Unit)
(sessionComplete : IO Unit)

@[reducible]
def LLVMTypeMap := RBMap String (Option llvm.llvm_type) Lean.strLt


structure ModuleVCGContext :=
(annotations : ModuleAnnotations)
-- ^ Annotations for module.
(decoder : decodex86.decoder )
-- ^ Machine code memory / decoder state
(symbolAddrMap : RBMap String (elf.word elf.elf_class.ELF64) Lean.strLt)
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
| argTypeUnsupported : llvm.ident -> llvm.llvm_type -> FnError
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
| unsupportedPhiVarType : llvm.ident → llvm.llvm_type → BlockError
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
| block : FnName → llvm.block_label → BlockError → ModuleError
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


def liftIO {α} (m : EIO IO.Error α) : EIO ModuleError α := 
  m.adaptExcept io


instance : MonadIO (EIO ModuleError) := {monadLift := @liftIO}


end ModuleError


-------------------------------------------------------
-- ModuleVCG (monad and some basic helpers)
-------------------------------------------------------


-- A monad for running verification of an entire module
-- TODO / FIXME we'll want to move away from EIO at, see
-- https://github.com/GaloisInc/reopt-vcg/pull/53#discussion_r408440682 
@[reducible]
def ModuleVCG := ReaderT ModuleVCGContext (EIO ModuleError)

namespace ModuleVCG
instance : Functor ModuleVCG := 
  inferInstanceAs (Functor (ReaderT ModuleVCGContext (EIO ModuleError)))
instance : Applicative ModuleVCG :=
  inferInstanceAs (Applicative (ReaderT ModuleVCGContext (EIO ModuleError)))
instance : Monad ModuleVCG :=
  inferInstanceAs (Monad (ReaderT ModuleVCGContext (EIO ModuleError)))

-- Run "standard" IO by wrapping any exceptions thrown in our Module.Error.IO wrapper.
def liftIO {α} (m : IO α) : ModuleVCG α := 
  monadLift $ m.adaptExcept ModuleError.io

instance ModuleVCG.MonadIO : MonadIO ModuleVCG := {monadLift := @ModuleVCG.liftIO}
instance : MonadReader ModuleVCGContext ModuleVCG :=
  inferInstanceAs (MonadReader ModuleVCGContext (ReaderT ModuleVCGContext (EIO ModuleError)))
end ModuleVCG


def runModuleVCG (ctx : ModuleVCGContext) (m : ModuleVCG Unit) : IO Unit := 
  EIO.adaptExcept ModuleError.toIOError (m.run ctx)

def vcgLog (msg : String) : ModuleVCG Unit := do 
  ctx ← read;
  when ctx.writeStderr $ 
    IO.println msg -- FIXME can't find the handle for stderr =\

-- A warning that stops execution until catch.
def functionError {α} (fnm : FnName) (e : FnError) : ModuleVCG α :=
  throw $ ModuleError.function fnm e

-- A warning that stops execution until catch.
def blockError {α} (fnm : FnName) (lbl : llvm.block_label) (e : BlockError) : ModuleVCG α :=
  throw $ ModuleError.block fnm lbl e

-- A warning that stops execution until catch.
def moduleThrow {α} (errMsg : String) : ModuleVCG α :=
  throw $ ModuleError.custom errMsg


-- Catch a VCG error, print it to the screen and keep going.
def moduleCatch (m : ModuleVCG Unit) :  ModuleVCG Unit :=
  λ ctx => do
    catch (m.run ctx) $ λ (e : ModuleError) =>
      when ctx.writeStderr $
        IO.println $ "Error: " ++ e.pp; -- FIXME use stderr or similar?
      ctx.errorCount.modify (λ n => n + 1)



-------------------------------------------------------
-- Annotated Block
-------------------------------------------------------

@[reducible]
def BlockLabelValMap := RBMap llvm.block_label llvm.value (λ x y => x < y)


structure AnnotatedBlock :=
(annotation: BlockAnn)
(label : llvm.block_label)
(phiVarMap : RBMap llvm.ident (SMTLIB.sort × BlockLabelValMap) (λ x y => x<y))
(stmts : List llvm.stmt)


/--  Maps LLM block labels to their associated annotations. --/
@[reducible]
def ReachableBlockAnnMap := RBMap llvm.block_label AnnotatedBlock (λ x y => x<y)

-------------------------------------------------------
-- BlockVCG
-------------------------------------------------------

abbrev MemAddr := Nat

-- Information that does not change during execution of a BlockVCG action.
structure BlockVCGContext :=
(mcModuleVCGContext : ModuleVCGContext)
  -- ^ Information at module level about CFG.
(llvmFunName : String)
  -- ^ Annotations for the current function.
(funBlkAnnotations : ReachableBlockAnnMap)
  -- ^ Annotations for blocks in the CFG.
(firstBlockLabel : llvm.block_label)
  -- ^ Label for first block in this function
(currentBlock : llvm.block_label)
  -- ^ Label for block we are verifying.
(callbackFns : ProverInterface)
  -- ^ Functions for interacting with SMT solver.
(mcBlockEndAddr : MemAddr)
  -- ^ The end address of the block.
(mcBlockMap : RBMap MemAddr MemoryAnn (λ x y => x < y))
  -- ^ Map from addresses to annotations of events on that address.

-- State that changes during execution of a BlockVCG action.
structure BlockVCGState :=
(mcCurAddr : MemAddr)
  -- ^ Address of the current instruction
(mcCurSize : Nat)
  -- ^ Size of current instruction.
--(mcX87Top : Nat) -- TODO...? later
  -- ^ Top index in x86 stack (starts at 7 and grows down).
(mcDF : Bool)
  -- ^ Direction flag
(mcCurRegs : Unit) -- FIXME(sjw) machine_state
  -- ^ Map registers to the SMT term.
(mcMemIndex : Nat)
  -- ^ Index of last defined memory object.
(mcEvents : List Unit) -- FIXME Unit => Event
  -- ^ Unprocessed events from last instruction.
(mcLocalIndex : Nat)
  -- ^ Index of next local variable for machine code.
-- (mcPendingAllocaOffsetMap : RBMap LocalIdent AllocaAnn (λ x y => x < y)) -- TODO use later
  -- ^ This is a map from allocation names to the annotations about their
  -- size and offset.
(llvmInstIndex : Nat)
  -- ^ Index of next LLVM instruction within block to execute
  -- Used for error reporting
--(activeAllocaSet : RBTree LocalIdent (λ x y => x < y)) -- TODO use later
 -- ^ Set of allocation names that are active.


def BlockVCG := ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))

namespace BlockVCG

instance : Monad BlockVCG :=
  inferInstanceAs (Monad (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))))

instance : MonadReader BlockVCGContext BlockVCG :=
  inferInstanceAs (MonadReader BlockVCGContext (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))))

instance : MonadState BlockVCGState BlockVCG :=
  inferInstanceAs (MonadState BlockVCGState (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))))

instance : MonadExcept String BlockVCG :=
  inferInstanceAs (MonadExcept String (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))))

instance : HasMonadLiftT IO BlockVCG :=
  inferInstanceAs (HasMonadLiftT IO (ReaderT BlockVCGContext (StateT BlockVCGState (ExceptT String IO))))


end BlockVCG


end ReoptVCG
