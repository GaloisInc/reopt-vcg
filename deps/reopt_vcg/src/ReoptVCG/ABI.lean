
import LeanLLVM.AST
import LeanLLVM.PP
import SmtLib.Smt
import X86Semantics.Common
import ReoptVCG.Annotations
import ReoptVCG.VCGBackend
import ReoptVCG.Types

-- ABI helpers

namespace NTuple

open Smt (SmtM SmtSort IdGen.empty RangeSort.bitvec SmtSort.bitvec)
open Smt.SmtSort -- (bool bitvec array bv64 tuple)

-- We always get a bool terminator, unit would also work, except
-- SMTLIB doesn't have one.  By convention we use 'false' if
-- constructing explicitly.  This could be nicer.
@[reducible]
def make ( ss : List SmtSort ) : SmtSort := List.foldr tuple bool ss 

@[reducible]
def value : forall (xs : List (Σs, Smt.Term s)), Smt.Term (make (List.map Sigma.fst xs)) 
| []      => Smt.false
| x :: xs => Smt.mkTuple _ _ x.snd (value xs)

def lens {a : Type} : forall (n : Nat) {ss : List SmtSort} (pf : n < ss.length)
                      (f : Smt.Term (ss.get n pf) -> a × Smt.Term (ss.get n pf)),
                      Smt.Term (NTuple.make ss) -> a × Smt.Term (NTuple.make ss) 
| n, [], pf, _, _            => absurd pf (Nat.notLtZero n)
| Nat.zero, s :: _, _, f, tm => 
  let old      := Smt.fst _ _ tm 
  let rest     := Smt.snd _ _ tm 
  let (r, new) := f old
  (r, Smt.mkTuple _ _ new rest) 
| Nat.succ n, s :: ss, pf, f, tm => 
  let pf' := cast (congrArg _ (List.length_cons s ss)) pf;
  let hd  := Smt.fst _ _ tm 
  let (r, rest) := lens n (Nat.lt_of_succ_lt_succ pf') f (Smt.snd _ _ tm)
  (r, Smt.mkTuple _ _ hd rest)

def index (n : Nat) {ss : List SmtSort} (pf : n < ss.length)
          (tm : Smt.Term (NTuple.make ss)) : Smt.Term (ss.get n pf) :=
 (lens n pf (fun tm' => (tm', tm')) tm).fst

end NTuple


-- ----------------------------------------------------------------------------------------
-- HasBVRepr and helpers

namespace LLVM

open Smt (SmtM SmtSort IdGen.empty RangeSort.bitvec SmtSort.bitvec)
open Smt.SmtSort -- (bool bitvec array bv64 tuple)

namespace FloatType

@[reducible]
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
def toSmtSort? : PrimType -> Option SmtSort
| integer i => if i > 0 then some (bitvec i) else none
| floatType ft => some (bitvec ft.nbits)
| _ => none


-- @[reducible]
-- def HasBVRepr (pt : PrimType) : Prop := Exists (fun s => toSMTRepr? pt = some s)

namespace HasBVRepr

-- protected 
-- def dec : forall (tp : PrimType), Decidable (HasBVRepr tp)
-- | integer i    => Nat.decLt _ _
-- | label        => isFalse (fun x => x) 
-- | token        => isFalse (fun x => x) 
-- | void         => isFalse (fun x => x) 
-- | floatType  _ => isTrue True.intro
-- | x86mmx       => isFalse (fun x => x) 
-- | metadata     => isFalse (fun x => x) 

-- instance {tp : PrimType} : Decidable (HasBVRepr tp) := HasBVRepr.dec tp

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

-- FIXME: gets around lean bug/missing feature with inductive datatypes containing others.
@[reducible]
def prim_toSmtSort? : LLVMType -> Option SmtSort
| prim pt => pt.toSmtSort?
| vector n (prim pt) =>
  (NTuple.make ∘ List.replicate n) <$> pt.toSmtSort?
| _       => none

-- N.B., Option is no longer a monad
@[reducible]
def prims_toSmtSort? : List LLVMType -> Option (List SmtSort)
| [] => some []
| t::ts => match prim_toSmtSort? t, prims_toSmtSort? ts with
           | some s, some ss => some $ s::ss
           | _, _ => none

@[reducible]
def toSmtSort? : LLVMType -> Option SmtSort
| ptr _   => some (bitvec 64)
| prim pt => pt.toSmtSort?
| vector n ty =>
  if n = 0
  then none -- FIXME
  else match prim_toSmtSort? ty with
       | none   => none
       | some s => some (NTuple.make (List.replicate n s))
| struct _ tys =>
  NTuple.make <$> (OptionM.run $ tys.data.mapM prim_toSmtSort?)
-- FIXME: lean bug/missing feature
| _ => none

def bitvec_toSmtSort? {n : Nat} (pf : n > 0) : 
    toSmtSort? (prim (PrimType.integer n)) = some (SmtSort.bitvec n) :=
    ifPos pf

def invert_vector_toSmtSort? {n : Nat} {lty : LLVMType} : forall {s : SmtSort} 
    ( pf : (vector n lty).toSmtSort? = some s ),
    -- also have n ≠ 0
    (Σ' s', prim_toSmtSort? lty = some s' ∧ s = NTuple.make (List.replicate n s')) := by
    match n with
    | 0 => intros pf; injection pf
    | Nat.succ m => 
      have H: (vector (Nat.succ m) lty).toSmtSort? = (match prim_toSmtSort? lty with
              | none   => none
              | some s => some (NTuple.make (List.replicate (Nat.succ m) s))) by rfl
      rw H
      match prim_toSmtSort? lty with
      | none => intros pf; injection pf
      | some s' => intros pf; injection pf with H'; exists s'; simp [H']


def invert_struct_toSmtSort? {b : Bool} {ltys : Array LLVMType} : forall {s : SmtSort} 
    ( pf : (struct b ltys).toSmtSort? = some s ),
    -- also have n ≠ 0
    (Σ' ss', OptionM.run (ltys.data.mapM prim_toSmtSort?) = some ss' ∧ s = NTuple.make ss') := by
      intros s
      have H: (struct b ltys).toSmtSort? = ( NTuple.make <$> (OptionM.run (ltys.data.mapM prim_toSmtSort?))) := rfl
      rw H
      match OptionM.run (ltys.data.mapM prim_toSmtSort?) with
      | none => intros pf; injection pf
      | some ss => intros pf; injection pf with H'; exists ss; rw H'; simp

section
open Smt (SmtSort.bitvec SmtSort.tuple SmtSort.bool)

-- returns lower n, remaining m
def split_word (n m : Nat) (pf_n : n > 0) (w : Smt.Term (SmtSort.bitvec (n + m))) : Smt.Term (SmtSort.bitvec n) × Smt.Term (SmtSort.bitvec m) :=
  let lower : Smt.Term (SmtSort.bitvec (n - 1 + 1 - 0)) := Smt.extract (n - 1) 0 w
  let lower_pf : n - 1 + 1 - 0 = n := sorryAx _
  let upper : Smt.Term (SmtSort.bitvec ((m + n) - 1 + 1 - n)) := Smt.extract ((m + n) - 1) n w
  let upper_pf : (m + n) - 1 + 1 - n = m := sorryAx _
  ( cast (congrArg (Smt.Term ∘ SmtSort.bitvec) lower_pf) lower
  , cast (congrArg (Smt.Term ∘ SmtSort.bitvec) upper_pf) upper)

-- FIXME: probably move
-- We use xucc to avoid creating 0 size bitvecs, which smtlib doesn't support
def unpackVecWord (w : Nat) (pf : w > 0) 
  : forall (n : Nat) (sw : Smt.Term (SmtSort.bitvec ((Nat.succ n) * w))),
    Smt.Term (NTuple.make (List.replicate (Nat.succ n) (SmtSort.bitvec w)))
| Nat.zero,   sw   => 
  -- FIXME: should be rfl?
  let pf : SmtSort.tuple (SmtSort.bitvec ((Nat.succ Nat.zero) * w)) SmtSort.bool = 
           NTuple.make (List.replicate (Nat.succ Nat.zero) (Smt.bitvec w)) := sorryAx _ 
  -- add the terminating bool
  cast (congrArg _ pf) (Smt.mkTuple _ _ sw Smt.false)

| Nat.succ n, sw => 
  let pf' : SmtSort.bitvec (Nat.succ (Nat.succ n) * w) = SmtSort.bitvec (w + (Nat.succ n) * w) := sorryAx _
  let (low, high) := split_word w ((Nat.succ n) * w) pf (cast (congrArg _ pf') sw)
  let rest        := unpackVecWord w pf n high
  let IH : Smt.tuple (Smt.bitvec w) (NTuple.make (List.replicate (Nat.succ n) (Smt.bitvec w))) = (NTuple.make (List.replicate (Nat.succ (Nat.succ n)) (Smt.bitvec w))) := sorryAx _
  cast (congrArg _ IH) (Smt.mkTuple _ _ low rest)

end


-- @[reducible]
-- def HasBVRepr : LLVMType -> Prop
-- | LLVM.LLVMType.ptr _  => True
-- | LLVM.LLVMType.prim pt  => PrimType.HasBVRepr pt
-- | LLVM.LLVMType.vector _ (LLVM.LLVMType.prim pt) => PrimType.HasBVRepr pt
-- | _ => False

namespace HasBVRepr

-- open LLVM.LLVMType
-- open LLVM.PrimType

-- protected 
-- def dec : forall (tp : LLVMType), Decidable (HasBVRepr tp)
-- | ptr t   => isTrue True.intro
-- | prim pt => PrimType.HasBVRepr.dec pt
-- | alias _        => isFalse (fun x => x)  
-- | array _ _      => isFalse (fun x => x)  
-- | funType _ _ _  => isFalse (fun x => x)
-- | struct _ _     => isFalse (fun x => x)  
-- | vector _ ty     => match ty with
--   | prim pt        => PrimType.HasBVRepr.dec pt
--   | ptr _          => isFalse (fun x => x)
--   | alias _        => isFalse (fun x => x)  
--   | array _ _      => isFalse (fun x => x)  
--   | funType _ _ _  => isFalse (fun x => x)
--   | struct _ _     => isFalse (fun x => x)  
--   | vector _ _     => isFalse (fun x => x)  

-- instance {tp : LLVMType} : Decidable (HasBVRepr tp) := HasBVRepr.dec tp

end HasBVRepr

end LLVMType

export LLVMType ( bitvec_toSmtSort? )

namespace PrimType

-- @[reducible]
-- def nbits : forall (tp : PrimType) (pf : PrimType.HasBVRepr tp), Nat
-- | LLVM.PrimType.integer i, _ => i
-- | LLVM.PrimType.floatType ft, _ => ft.nbits

end PrimType

namespace LLVMType

-- @[reducible]
-- def nbits : forall (tp : LLVMType) (pf : LLVMType.HasBVRepr tp), Nat
-- | LLVM.LLVMType.ptr _, _  => 64
-- | LLVM.LLVMType.prim pt, pf => pt.nbits pf
-- | LLVM.LLVMType.vector n (LLVM.LLVMType.prim pt), pf => n * pt.nbits pf

end LLVMType
end LLVM

namespace ReoptVCG

open LLVM (Typed LLVMType LLVMType.prim LLVMType.vector LLVMType.ptr
           PrimType PrimType.integer PrimType.floatType)

open LLVM.LLVMType (bitvec_toSmtSort?)

-- open LLVM.LLVMType (HasBVRepr)
open x86 (concrete_reg)
open mc_semantics.type

namespace Internal

open mc_semantics
open Smt (SmtM SmtSort IdGen.empty RangeSort.bitvec SmtSort.bitvec SmtSort.tuple SmtSort.bool)


-- FIXME: move
def float_type_nbits_le_avx_width : forall (ft : LLVM.FloatType), ft.nbits <= x86.avx_width 
| LLVM.FloatType.half     => rfl
| LLVM.FloatType.float    => rfl
| LLVM.FloatType.double   => rfl
| LLVM.FloatType.fp128    => rfl
| LLVM.FloatType.x86FP80  => rfl
| LLVM.FloatType.ppcFP128 => rfl

-- Shared between arg and ret
def matchArgToReg {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) (s : SmtSort) (pf : lty.toSmtSort? = some s), 
        a -> (x86.vcg.RegState -> Smt.Term s) -> m b ) :
  Typed a →
  List x86.reg64 →  -- ^ Remaining registers available for arguments.
  List x86.avxreg →  -- ^ Remaining float registers available for arguments.
  m (b × List x86.reg64 × List x86.avxreg)
| ⟨LLVMType.prim (PrimType.integer n), v⟩, regs, fpregs =>
  match regs with
  | [] => err "Ran out of GP registers"
  | (reg::restRegs) => do  
    let mkReg (H : n <= 64) (rs : x86.vcg.RegState) := 
       if H': 64 = n
       then let pf := congrArg (fun i => Smt.Term (Smt.bitvec i)) H'; 
            cast pf (rs.get_reg64 reg)
       else x86.vcg.bitvec.trunc n H (rs.get_reg64 reg)
      
    let f' <- if H : n <= 64 then pure (mkReg H) else err "Integer argument too large"

    if Hi : n > 0 
      then do
        let r <- f (LLVMType.prim (PrimType.integer n)) _ (bitvec_toSmtSort? Hi) v f'
        pure (r, restRegs, fpregs)
      else err "Zero-sized integer"

| ⟨LLVMType.vector 8 (LLVMType.prim (PrimType.floatType LLVM.FloatType.double)), v⟩, regs, fpregs =>
  match fpregs with
  | [] => err "Ran out of FP registers"
  | (reg::restFPRegs) => do
    let f' := fun (rs : x86.vcg.RegState) => LLVM.LLVMType.unpackVecWord 64 rfl 7 (rs.get_avxreg' reg)
    let r <- f (LLVMType.vector 8 (LLVMType.prim (PrimType.floatType LLVM.FloatType.double))) 
               _ rfl v f'
    pure (r, regs, restFPRegs)

| ⟨PrimType.floatType ft, v⟩, regs, fpregs =>
  match fpregs with
  | [] => err "Ran out of FP registers"
  | (reg::restFPRegs) => do
    let rv := fun (rs : x86.vcg.RegState) => 
                  x86.vcg.bitvec.trunc ft.nbits (float_type_nbits_le_avx_width ft) 
                                       (rs.get_avxreg' reg)
    let r <- f (PrimType.floatType ft) _ rfl v rv
    pure (r, regs, restFPRegs)

| ⟨tp, _⟩, _, _ => err ("Unsupported type: " ++ ppLLVM tp)


def forEachArgImpl {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( s : SmtSort ) (pf : lty.toSmtSort? = some s),
        a -> (x86.vcg.RegState -> Smt.Term s) -> m b ) :
  List b →
  List (Typed a) →
  List x86.reg64 →  -- ^ Remaining registers available for arguments.
  List x86.avxreg →  -- ^ Remaining float registers available for arguments.
  m (List b)
| revAcc, [], _, _ => pure revAcc.reverse
| revAcc, (arg :: restArgs), regs, fpregs => do
  let (r, restGPRegs, restFPRegs) <- matchArgToReg err f arg regs fpregs
  forEachArgImpl err f (r :: revAcc) restArgs restGPRegs restFPRegs

-- FIXME: merge with above
def forReturnValImpl {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( s : SmtSort ) (pf : lty.toSmtSort? = some s),
        a -> (x86.vcg.RegState -> Smt.Term s) -> m b )
  (arg : Typed a)
  (regs : List x86.reg64)     -- ^ Remaining registers available for arguments.
  (fpregs : List x86.avxreg)  -- ^ Remaining float registers available for arguments.
  : m b := do
  let (r, _restGPRegs, _restFPRegs) <- matchArgToReg err f arg regs fpregs
  pure r

end Internal

open Smt (SmtSort)

def forEachArg {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( s : SmtSort ) (pf : lty.toSmtSort? = some s),
        a -> (x86.vcg.RegState -> Smt.Term s) -> m b )
  (args : List (Typed a)) : m (List b) := 
  Internal.forEachArgImpl err f [] args x86ArgGPRegs x86ArgFPRegs

theorem map_map {α β γ : Type} (f : α -> β) (g : β -> γ) (xs : List α) : 
        List.map g (List.map f xs) = List.map (g ∘ f) xs := by
  induction xs with
  | nil => exact rfl
  | cons x xs' ih => 
    have rl : g (f x) :: List.map g (List.map f xs') = (g ∘ f) x :: List.map (g ∘ f) xs'
      := by rw ih
    exact rl

theorem map_ext {α β : Type} (f g : α -> β) (pf : forall x, f x = g x) (xs : List α) :
        List.map f xs = List.map g xs := by
  induction xs with
  | nil => exact rfl
  | cons x xs' ih => 
    have rl : f x :: List.map f xs' = g x :: List.map g xs' := by rw ih; rw (pf x)
    exact rl

-- set_option pp.raw true

def forReturnVal {a b : Type} {m : Type -> Type} [Monad m] (err : forall {c}, String -> m c)
  ( f : forall (lty : LLVMType) ( s : SmtSort ) (pf : lty.toSmtSort? = some s),
        a -> (x86.vcg.RegState -> Smt.Term s) -> m b )
  (arg : Typed a) : m b := 
  match arg.type with
  | LLVM.LLVMType.struct b tys => do
    -- we remake the proof later, plumbing it through would be a pain (although more correct)
    let fake_f _lty (s : SmtSort)  _pf _unit (mk : x86.vcg.RegState -> Smt.Term s) := pure (Sigma.mk s mk)
    -- unpack the struct and assign to return registers
    let mks : List (Σ s, x86.vcg.RegState -> Smt.Term s) <- 
       Internal.forEachArgImpl err fake_f [] (List.map (fun lty => ⟨lty, ()⟩) tys.data) x86ResultGPRegs x86ResultFPRegs

    let mk : x86.vcg.RegState -> Smt.Term (NTuple.make (List.map Sigma.fst mks)) := fun regs => 

      let tm -- : Smt.Term (NTuple.make (List.map Sigma.fst (List.map (fun (Sigma.mk s mkf) => Sigma.mk s (mkf regs)) mks)))
        := NTuple.value (List.map (fun (Sigma.mk s mkf) => ⟨s, mkf regs⟩) mks)

      -- let pf : List.map Sigma.fst (List.map (fun (Sigma.mk s mkf) => Sigma.mk s (mkf regs)) mks)
      --        = List.map Sigma.fst mks := by 
      --    rw (map_map _ _ mks)
      --    apply map_ext
      --    intros x
      --    cases x
      --    exact rfl

      -- let pf' : Smt.Term (NTuple.make (List.map Sigma.fst (List.map (fun (Sigma.mk s mkf) => Sigma.mk s (mkf regs)) mks)))
      --        = Smt.Term (NTuple.make (List.map Sigma.fst mks)) := 
      --   congrArg (Smt.Term ∘ NTuple.make) pf
  
      let pf' := by 
         rw (map_map _ _ mks)
         rw map_ext
         intros x
         cases x
         exact rfl

      cast pf' tm 

    if pf : arg.type.toSmtSort? = some (NTuple.make (List.map Sigma.fst mks))
    then f _ _ pf arg.value mk 
    else err ("Internal error: type mismatch in forReturnVal")

  | _            => Internal.forReturnValImpl err f arg x86ResultGPRegs x86ResultFPRegs






end ReoptVCG





