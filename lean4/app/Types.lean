import Galois.Data.ByteArray
import LeanLLVM.AST
import Main.Elf
import ReoptVCG.Annotations
import SMTLIB.Syntax


namespace ReoptVCG

structure MemSegOffset :=
(val : UInt64)  -- FIXME

def Ty := Unit -- FIXME

-- FIXME double check on which interface/API/etc to use here =\
-- The SMTLIB.Raw namespace feels like it has the direct equivalents
-- to the What4.Protocol.SMTLib2.Syntax module in Haskell, but...
-- it's the "Raw" interface which feels a little off...
open SMTLIB.Raw 

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
          
def FunctionName := String
def BlockLabel := llvm.ident

structure ProverInterface :=
(addCommandCallback : command → IO Unit)
(proveFalseCallback : term const_sort.smt_bool → String → IO Unit)
(proveTrueCallback  : term const_sort.smt_bool → String → IO Unit)
-- (blockErrorCallback : Int → MemSegmentOff 64 → String → IO Unit)

structure ProverSessionGenerator :=
(blockCallback : FunctionName → BlockLabel → (ProverInterface → IO Unit) → IO Unit)
(sessionComplete : IO Unit)

structure ModuleVCGContext :=
(annotations : ModuleAnnotations)
-- ^ Annotations for module.
(memory : elf.elfmem)
-- ^ Machine code memory
(symbolAddrMap : RBMap ByteArray MemSegOffset ByteArray.lt)
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
(moduleTypeMap : (RBMap llvm.ident Ty (λ x y => x < y))) -- FIXME
-- ^ type map for module.

end ReoptVCG
