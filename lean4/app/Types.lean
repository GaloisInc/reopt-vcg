import Galois.Data.ByteArray
import LeanLLVM.AST
import LeanLLVM.PP
import Main.Elf
import ReoptVCG.Annotations
import SMTLIB.Syntax

-- TODO move these (or similar fns) to lean-llvm
def llvm.ident.pp := pp.render ∘ llvm.pp_ident
def llvm.llvm_type.pp := pp.render ∘ llvm.pp_type
def llvm.block_label.pp := pp.render ∘ llvm.pp_label

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
structure ProverInterface :=
(addCommandCallback : command → IO Unit)
(proveFalseCallback : term const_sort.smt_bool → String → IO Unit)
(proveTrueCallback  : term const_sort.smt_bool → String → IO Unit)
-- (blockErrorCallback : Int → MemSegmentOff 64 → String → IO Unit)

structure ProverSessionGenerator :=
(blockCallback : FnName → llvm.block_label → (ProverInterface → IO Unit) → IO Unit)
(sessionComplete : IO Unit)

@[reducible]
def LLVMTypeMap := RBMap String (Option llvm.llvm_type) Lean.strLt


structure ModuleVCGContext :=
(annotations : ModuleAnnotations)
-- ^ Annotations for module.
(memory : elf.elfmem)
-- ^ Machine code memory
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

instance ModuleVCG.MonadIO : MonadIO ModuleVCG := {monadLift := @liftIO}
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

structure AnnotatedBlock :=
(annotation: BlockAnn)
(label : llvm.block_label)
(phiVarMap : RBMap String Unit Lean.strLt) -- FIXME
(stmts : List Unit) -- FIXME


end ReoptVCG
