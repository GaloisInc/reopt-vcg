
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import SMTLIB.Syntax
import ReoptVCG.Types

namespace ReoptVCG

open llvm (llvm_type typed prim_type value)

def llvmReturn (mlret : Option (typed value)) : BlockVCG Unit := throw "Not done yet"

-- | Convert LLVM type to SMT sort.
def asSMTSort : llvm_type -> Option SMT.sort
| llvm.llvm_type.ptr_to _  => some (SMT.sort.bitvec 64)
| llvm.llvm_type.prim_type (llvm.prim_type.integer i) =>
  if i > 0 then some (SMT.sort.bitvec i) else none
| _ => none

def coerceToSMTSort (ty : llvm_type) : BlockVCG SMT.sort :=
  match asSMTSort ty with
  | some tp => pure tp
  | none    => throw ("Unexpected type ")

section
open llvm.instruction

-- def defineTerm {s : SMT.sort) : llvm.ident -> SMT.term s -> BlockVCG Unit :=
  
def stepNextStmt (stmt : llvm.stmt) : BlockVCG Bool := do
  match stmt.instr with
  | ret v    => llvmReturn (some v) $> false
  | ret_void => llvmReturn none     $> false
  -- | arith aop { type := lty, value := lhs } rhs => do
  --   tp <- coerceToSMTSort lty;
  --   lhsv <- primEval lty lhs;
  --   rhsv <- primEval lty rhs; -- same type as lhs

  | _ => throw "unimplemented" 


--   | bit : bit_op -> typed value -> value -> instruction
--   | conv : conv_op -> typed value -> llvm_type -> instruction
--   | call (tailcall : Bool) : Option llvm_type -> value -> Array (typed value) -> instruction
--   | alloca : llvm_type -> Option (typed value) -> Option Nat -> instruction
--   | load : typed value -> Option atomic_ordering -> Option Nat /- align -/ -> instruction
--   | store : typed value -> typed value -> Option Nat /- align -/ -> instruction
-- /-
--   | fence : option string -> atomic_ordering -> instruction
--   | cmp_xchg (weak : bool) (volatile : bool) : typed value -> typed value -> typed value
--             -> option string -> atomic_ordering -> atomic_ordering -> instruction
--   | atomic_rw (volatile : bool) : atomic_rw_op -> typed value -> typed value
--             -> option string -> atomic_ordering -> instruction
-- -/
--   | icmp : icmp_op -> typed value -> value -> instruction
--   | fcmp : fcmp_op -> typed value -> value -> instruction
--   | phi : llvm_type -> Array (value × block_label) -> instruction
--   | gep (bounds : Bool) : typed value -> Array (typed value) -> instruction
--   | select : typed value -> typed value -> value -> instruction
--   | extract_value : typed value -> List Nat -> instruction
--   | insert_value : typed value -> typed value -> List Nat -> instruction
--   | extract_elt : typed value -> value -> instruction
--   | insert_elt : typed value -> typed value -> value -> instruction
--   | shuffle_vector : typed value -> value -> typed value -> instruction
--   | jump : block_label -> instruction
--   | br : typed value -> block_label -> block_label -> instruction
--   | invoke : llvm_type -> value -> List (typed value) -> block_label -> block_label -> instruction
--   | comment : String -> instruction
--   | unreachable
--   | unwind
--   | va_arg : typed value -> llvm_type -> instruction
--   | indirect_br : typed value -> List block_label -> instruction
--   | switch : typed value -> block_label -> List (Nat × block_label) -> instruction
--   | landing_pad : llvm_type -> Option (typed value) -> Bool -> List (clause × typed value) -> instruction
--   | resume : typed value -> instruction
end
  

end ReoptVCG
