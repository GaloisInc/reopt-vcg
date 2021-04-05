
import LeanLLVM.AST
import LeanLLVM.PP
import SmtLib.Smt
import X86Semantics.Common
import ReoptVCG.Annotations

-- ABI helpers


-- ----------------------------------------------------------------------------------------
-- HasBVRepr and helpers

namespace LLVM

namespace PrimType

@[reducible]
def HasBVRepr : PrimType -> Prop
| integer i => i > 0
| floatType _ => True
| _ => False

namespace HasBVRepr

protected 
def dec : forall (tp : PrimType), Decidable (HasBVRepr tp)
| integer i    => Nat.decLt _ _
| label        => isFalse (fun x => x) 
| token        => isFalse (fun x => x) 
| void         => isFalse (fun x => x) 
| floatType  _ => isTrue True.intro
| x86mmx       => isFalse (fun x => x) 
| metadata     => isFalse (fun x => x) 

instance {tp : PrimType} : Decidable (HasBVRepr tp) := HasBVRepr.dec tp

end HasBVRepr

end PrimType

namespace LLVMType

-- -- The restriction to vecs of prims gets around Lean not supporting
-- -- recursion over types containing arrays
-- @[reducible]
-- def HasBVRepr : LLVMType -> Prop
-- | LLVM.LLVMType.ptr _  => True
-- | LLVM.LLVMType.prim pt  => PrimType.HasBVRepr pt
-- | LLVM.LLVMType.vector _ ty => match ty with
--   | LLVM.LLVMType.prim pt => PrimType.HasBVRepr pt
--   | _ => False
-- | _ => False

@[reducible]
def HasBVRepr : LLVMType -> Prop
| LLVM.LLVMType.ptr _  => True
| LLVM.LLVMType.prim pt  => PrimType.HasBVRepr pt
| LLVM.LLVMType.vector _ (LLVM.LLVMType.prim pt) => PrimType.HasBVRepr pt
| _ => False


namespace HasBVRepr

open LLVM.LLVMType
open LLVM.PrimType

protected 
def dec : forall (tp : LLVMType), Decidable (HasBVRepr tp)
| ptr t   => isTrue True.intro
| prim pt => PrimType.HasBVRepr.dec pt
| alias _        => isFalse (fun x => x)  
| array _ _      => isFalse (fun x => x)  
| funType _ _ _  => isFalse (fun x => x)
| struct _ _     => isFalse (fun x => x)  
| vector _ ty     => match ty with
  | prim pt        => PrimType.HasBVRepr.dec pt
  | ptr _          => isFalse (fun x => x)
  | alias _        => isFalse (fun x => x)  
  | array _ _      => isFalse (fun x => x)  
  | funType _ _ _  => isFalse (fun x => x)
  | struct _ _     => isFalse (fun x => x)  
  | vector _ _     => isFalse (fun x => x)  

instance {tp : LLVMType} : Decidable (HasBVRepr tp) := HasBVRepr.dec tp

end HasBVRepr

end LLVMType

namespace FloatType

def nbits : FloatType -> Nat
| LLVM.FloatType.half     => 16
| LLVM.FloatType.float    => 32
| LLVM.FloatType.double   => 64 
| LLVM.FloatType.fp128    => 128
| LLVM.FloatType.x86FP80  => 80
| LLVM.FloatType.ppcFP128 => 128

end FloatType

namespace PrimType

@[reducible]
def nbits : forall (tp : PrimType) (pf : PrimType.HasBVRepr tp), Nat
| LLVM.PrimType.integer i, _ => i
| LLVM.PrimType.floatType ft, _ => ft.nbits

end PrimType

namespace LLVMType

@[reducible]
def nbits : forall (tp : LLVMType) (pf : LLVMType.HasBVRepr tp), Nat
| LLVM.LLVMType.ptr _, _  => 64
| LLVM.LLVMType.prim pt, pf => pt.nbits pf
| LLVM.LLVMType.vector n (LLVM.LLVMType.prim pt), pf => n * pt.nbits pf

end LLVMType
end LLVM

namespace ReoptVCG

open LLVM (Typed LLVMType LLVMType.prim LLVMType.vector LLVMType.ptr
           PrimType PrimType.integer PrimType.floatType)

open Smt (SmtM SmtSort SmtSort.bool SmtSort.bitvec SmtSort.array SmtSort.bv64 IdGen.empty RangeSort.bitvec)
open LLVM.LLVMType (HasBVRepr)
open x86 (concrete_reg)
open mc_semantics.type

namespace Internal

def forEachArgImpl {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( H : HasBVRepr lty ), a -> concrete_reg (bv (lty.nbits H)) -> m b ) :
  List b →
  List (Typed a) →
  List x86.reg64 →  -- ^ Remaining registers available for arguments.
  List x86.avxreg →  -- ^ Remaining float registers available for arguments.
  m (List b)
| revAcc, [], _, _ => pure revAcc.reverse
| revAcc, (⟨LLVMType.prim (PrimType.integer 64), v⟩::restArgs), regs, fpregs =>
  match regs with
  | [] => err "Ran out of GP registers"
  | (reg::restRegs) => do  
    let r <- f (LLVMType.prim (PrimType.integer 64)) rfl v reg
    forEachArgImpl err f (r :: revAcc) restArgs restRegs fpregs

| revAcc, ( ⟨LLVMType.vector 8 (LLVMType.prim (PrimType.floatType LLVM.FloatType.double)), v⟩ :: restArgs), regs, fpregs =>
  match fpregs with
  | [] => err "Ran out of FP registers"
  | (reg::restFPRegs) => do
    let r <- f (LLVMType.vector 8 (LLVMType.prim (PrimType.floatType LLVM.FloatType.double))) True.intro v reg
    forEachArgImpl err f (r :: revAcc) restArgs regs restFPRegs

| _, (⟨tp, _⟩::_), _, _ => err ("Unsupported type: " ++ ppLLVM tp)

end Internal

def forEachArg {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( H : HasBVRepr lty ), a -> concrete_reg (bv (lty.nbits H)) -> m b )
  (args : List (Typed a)) : m (List b) := 
  Internal.forEachArgImpl err f [] args x86ArgGPRegs x86ArgFPRegs

end ReoptVCG




