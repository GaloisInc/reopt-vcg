
import Galois.Data.List
import Galois.Data.RBMap
import SmtLib.Syntax
import SmtLib.BitVec
import Std.Data.RBMap
import Std.Data.RBTree
import Galois.Data.DRBMap


def upd.{u, v} {α : Type u} [DecidableEq α] {β: α -> Type v} (f : forall v, β v) (k : α) (v : β k) : forall v, β v :=       
  fun k' => if H : k = k' then cast (congrArg β H) v else f k'

namespace upd

-- @[macroInline] def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
-- Decidable.casesOn h (fun hnc => e) (fun hc => t)

-- theorem ifNeg {c : Prop} [h : Decidable c] (hnc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e :=
universes u v
variables {α : Type u} [DecidableEq α] {β: α -> Type v}


theorem updAtOther {k k'} (f : forall v, β v) (v : β k) (pf : k ≠ k') : (upd f k v) k' = f k' :=
  difNeg pf       


end upd


def updMap {α β : Type} [DecidableEq α] (f : α -> Option β) (k : α) (v : β) :  α -> Option β :=
  upd f k (some v) 

namespace Std

namespace DRBMap

universes u v

variables {α : Type u} {β : α → Type v} {lt : α → α → Bool}

def keys : DRBMap α β lt → List α 
| ⟨t, _⟩ => t.revFold (fun ps k v => k::ps) []

-- swf dcong { δ : α -> Type } : forall (m : DRBMap α β lt) 
--           (f : forall k, m.contains k -> β k = δ k), DRBMap α δ lt



end DRBMap
end Std

namespace Smt

open Std (RBMap DRBMap)

structure Array (α β : Type) :=
(elems : List (α × β))
(dflt : β)

section
variables {α β : Type}

def Array.decEq [DecidableEq α]
                [DecidableEq β]
                (arr1 arr2 : Array α β) : Decidable (arr1 = arr2) :=
Array.casesOn arr1 $ λ elems1 dflt1 => Array.casesOn arr2 $ λ elems2 dflt2 =>
  match (decEq elems1 elems2) with
  | (isTrue e₁) =>
    match (decEq dflt1 dflt2) with
    | (isTrue e₂)  => isTrue (Eq.recOn e₁ (Eq.recOn e₂ rfl))
    | (isFalse n₂) => isFalse (fun h => Array.noConfusion h (fun e₁' e₂' => absurd e₂' n₂))
  | (isFalse n₁) => isFalse (fun h => Array.noConfusion h (fun e₁' e₂' => absurd e₁' n₁))


def Array.Less [HasLess α] [HasLess β] : Array α β → Array α β → Prop
| a1, a2 => (a1.elems, a1.dflt) < (a2.elems, a2.dflt)

instance Array.HasLess [HasLess α] [HasLess β] : HasLess (Array α β) :=
⟨@Array.Less α β _ _⟩


def Array.decLt [DecidableEq α]
                [DecidableEq β]
                [HasLess α] 
                [HasLess β]
                [forall (a1 a2 : α), Decidable (a1 < a2)]
                [forall (b1 b2 : β), Decidable (b1 < b2)]
                (arr1 arr2 : Array α β) : Decidable (arr1 < arr2) :=
Array.casesOn arr1 $ λ elems1 dflt1 => Array.casesOn arr2 $ λ elems2 dflt2 =>
  let prodLtDec : ∀ (p1 p2 : (α × β)), Decidable (p1 < p2) := prodHasDecidableLt;
  let listLtDec : ∀ (l1 l2 : List (α × β)), Decidable (l1 < l2) := List.hasDecidableLt;
  inferInstanceAs (Decidable ((elems1, dflt1) < (elems2, dflt2)))

end




@[reducible]
protected def SmtSort.denote : SmtSort → Type
| SmtSort.bool => Bool
| SmtSort.bitvec n => BitVec n
| SmtSort.array k v => Array k.denote v.denote


namespace SmtSort


private def denoteDecidableEq : forall (s : SmtSort), DecidableEq s.denote
| SmtSort.bool => Bool.DecidableEq
| SmtSort.bitvec n => BitVec.DecidableEq
| SmtSort.array k v =>
  let kHasLess := denoteDecidableEq k;
  let vHasLess := denoteDecidableEq v;
  Array.decEq


instance denote.DecidableEq : forall (s : SmtSort), DecidableEq s.denote :=
  denoteDecidableEq

inductive BoolLess : Bool → Bool → Prop
| trueLess (b : Bool) : BoolLess true b

private def boolLessImplTrue : forall {b1 b2 : Bool}, BoolLess b1 b2 → b1 = true
| true, _, _ => rfl

private def boolDecidableLt (x y : Bool) : Decidable (BoolLess x y) :=
@Bool.casesOn
  (λ b => Decidable (BoolLess b y))
  x
  (isFalse (λ (h : BoolLess false y) => Bool.noConfusion (boolLessImplTrue h)))
  (isTrue (BoolLess.trueLess y))

private def denoteHasLess : forall (s: SmtSort) , HasLess s.denote
| SmtSort.bool => {Less := BoolLess}
| SmtSort.bitvec n => {Less := @BitVec.ult n}
| SmtSort.array k v =>
  let kHasLess := denoteHasLess k;
  let vHasLess := denoteHasLess v;
  Array.HasLess


instance denote.HasLess : forall (s : SmtSort), HasLess s.denote :=
denoteHasLess


private def denoteDecidableLt : forall (s : SmtSort), forall (x y : s.denote), Decidable (x < y)
| SmtSort.bool => boolDecidableLt
| SmtSort.bitvec n => @BitVec.decidable_ult n
| SmtSort.array k v =>
  let kH := denoteDecidableLt k;
  let vH := denoteDecidableLt v;
  Array.decLt


instance denote.DecidableLt : forall (s : SmtSort), forall (x y : s.denote), Decidable (x < y) :=
denoteDecidableLt

private def denoteInhabited : forall (s : SmtSort), Inhabited s.denote
| SmtSort.bool => {default := true}
| SmtSort.bitvec n => {default := 0}
| SmtSort.array k v => {default := ⟨[], (denoteInhabited v).default⟩}

instance denote.Inhabited : forall (s : SmtSort), Inhabited s.denote :=
denoteInhabited

end SmtSort

namespace Array
section
variables {α β : Type}

protected def toList (a : Array α β) : List (α × β) :=
a.elems

protected def keys (a : Array α β) : List α :=
a.elems.map (λ e => e.fst)



protected def select [HasBeq α] (a : Array α β) (k : α) : β :=
match a.elems.lookup k with
| some v => v
| none => a.dflt


protected def store [HasLess α] [forall (x y:α), Decidable (x < y)] (a : Array α β) (k : α) (v : β) : Array α β :=
{a with elems := SortedAList.insert k v a.elems}

private def checkEntry [HasBeq α] (a : Array α β) (k : α) (p : β → Bool) : Bool :=
match a.elems.lookup k with
| some v => p v
| none => false

end

private def bvEqRangeAux {β n} [HasBeq β] (a1 a2 : Array (BitVec n) β) (low : BitVec n) : Nat → Bool
| Nat.zero => a1.select 0 == a2.select 0
| Nat.succ i =>
  let idx := low + (BitVec.ofNat n i) + 1;
  a1.select idx == a2.select idx && bvEqRangeAux i

def bvEqRange {β n} [HasBeq β] (a1 a2 : Array (BitVec n) β) (low high : BitVec n) : Bool :=
if BitVec.ult high low then true
else
  let rangeSize := high - low;
  bvEqRangeAux a1 a2 low rangeSize.toNat


def eqRange {β} [HasBeq β] :
  forall (s : RangeSort),
  Array s.sort.denote β →
  Array s.sort.denote β →
  s.sort.denote →
  s.sort.denote → Bool
| RangeSort.bitvec n, a1, a2, low, high => bvEqRange a1 a2 low high

end Array


namespace Raw

def Env := Symbol -> Option ConstSort

--------------------------------------------------------------------------------
-- Well sorted terms
--
-- Because we have typed terms, well-sortedness boils down to the
-- variables having the claimed sort.

namespace Ident

inductive WF : forall {cs : ConstSort}, Env → Ident cs → Prop
| symbol : ∀ {e : Env} {cs : ConstSort} {x : Symbol}, e x = some cs → WF e (Ident.symbol cs x)
| builtin : ∀ (e : Env) {cs : ConstSort} (b : BuiltinIdent cs), WF e (Ident.builtin b)

end Ident

namespace Term

inductive WF : forall {cs : ConstSort}, Env → Term cs → Prop
| const : ∀ (e : Env) {s : SmtSort} (sc : SpecConst s), WF e (Term.const s sc)
| ident : ∀ {e : Env} {cs : ConstSort} {x : Ident cs}, Ident.WF e x → WF e (Term.ident x)
| app   : ∀ {e : Env} {s : SmtSort} {cs : ConstSort}
         {t1 : Term (ConstSort.fsort s cs)}
         {t2 : Term (ConstSort.base s)},
  WF e t1 →
  WF e t2 →
  WF e (Term.app t1 t2)
| smtLet : ∀ {e : Env} {s1 s2 : SmtSort} {x : Symbol}
           {t1 : Term (ConstSort.base s1)}
           {t2 : Term (ConstSort.base s2)},
  WF e t1 →
  WF (updMap e x (Raw.ConstSort.base s1)) t2 →
  WF e (Term.smtLet x t1 t2)
| smtForall : ∀ {e : Env} {s : SmtSort} {x : SortedVar s} {t : Term ConstSort.bool},
  WF (updMap e x.var (Raw.ConstSort.base s)) t →
  WF e (Term.smtForall x t)
| smtExists : ∀ {e : Env} {s : SmtSort} {x : SortedVar s} {t : Term ConstSort.bool},
  WF (updMap e x.var (Raw.ConstSort.base s)) t →
  WF e (Term.smtExists x t)

end Term  


namespace ConstSort

@[reducible]
protected def denote : ConstSort → Type
| ConstSort.base s => s.denote
| ConstSort.fsort a b => a.denote → b.denote

end ConstSort

namespace VarArgs

private def varArgsPred (α : Type) : Nat → Type
| 0 => Bool
| Nat.succ n => α → varArgsPred n


private def distinctList {α : Type} [DecidableEq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote → (nary s SmtSort.bool n).denote
| 0, args => distinctList args
| Nat.succ n, args => λ a => (distinct n) (a::args)

end VarArgs


private def mkDistinct (s : SmtSort) (n : Nat) : (nary s SmtSort.bool n).denote :=
VarArgs.distinct s n []


@[reducible]
protected def BuiltinIdent.denote : forall cs, BuiltinIdent cs → cs.denote
-- * Core theory
| _, BuiltinIdent.true => true
| _, BuiltinIdent.false => false
| _, BuiltinIdent.not => not
| _, BuiltinIdent.impl => λ p q => !p || q
| _, BuiltinIdent.and => and
| _, BuiltinIdent.or => or
| _, BuiltinIdent.xor => xor
| _, BuiltinIdent.eq s => λ x y => x = y
| _, BuiltinIdent.smtIte s => λ t x y => if t then x else y
| _, BuiltinIdent.distinct s n => mkDistinct s n

| _, BuiltinIdent.select _ _           => Array.select
| _, BuiltinIdent.store  _ _           => Array.store
| _, BuiltinIdent.eqrange k _          => Array.eqRange k

-- -- * BitVecs
-- -- hex/binary literals
| _, BuiltinIdent.concat _ _           => BitVec.append
| _, BuiltinIdent.extract n i j        => BitVec.extract i j
-- -- unops
| _, BuiltinIdent.bvnot   _            => BitVec.not
| _, BuiltinIdent.bvneg   _            => BitVec.neg
-- -- binops                   
| _, BuiltinIdent.bvand   _            => BitVec.and
| _, BuiltinIdent.bvor    _            => BitVec.or
| _, BuiltinIdent.bvadd   _            => BitVec.add
| _, BuiltinIdent.bvmul   _            => BitVec.mul
| _, BuiltinIdent.bvudiv  _            => BitVec.udiv
| _, BuiltinIdent.bvurem  _            => BitVec.urem
| _, BuiltinIdent.bvshl   _            => λ b i => BitVec.shl b i.toNat
| _, BuiltinIdent.bvlshr  _            => λ b i => BitVec.ushr b i.toNat
-- -- comparison               
| _, BuiltinIdent.bvult   _            => λ b1 b2 => decide (BitVec.ult b1 b2)

| _, BuiltinIdent.bvnand  _            => λ b1 b2 => BitVec.not (BitVec.and b1 b2)
| _, BuiltinIdent.bvnor   _            => λ b1 b2 => BitVec.not (BitVec.or b1 b2)
| _, BuiltinIdent.bvxor   _            => BitVec.xor
| _, BuiltinIdent.bvxnor  _            => λ b1 b2 => BitVec.not (BitVec.xor b1 b2)
| _, BuiltinIdent.bvcomp  _            => λ b1 b2 => if b1 = b2 then 1 else 0
| _, BuiltinIdent.bvsub   _            => BitVec.sub
| _, BuiltinIdent.bvsdiv  _            => BitVec.sdiv
| _, BuiltinIdent.bvsrem  _            => BitVec.srem
| _, BuiltinIdent.bvsmod  _            => BitVec.smod
| _, BuiltinIdent.bvashr  _            => λ b i => BitVec.sshr b i.toNat

| _, BuiltinIdent.repeat i _           => λ b => BitVec.repeat b i

| _, BuiltinIdent.zeroExtend  i n     => λ b => b.uresize (n + i)
| _, BuiltinIdent.signExtend  i n     => λ b => b.sresize (n + i)
| _, BuiltinIdent.rotateLeft  i _     => BitVec.rotateLeft i
| _, BuiltinIdent.rotateRight i _     => BitVec.rotateRight i

| _, BuiltinIdent.bvule _              => λ x y => decide (BitVec.ule x y)
| _, BuiltinIdent.bvugt _              => λ x y => decide (BitVec.ugt x y)
| _, BuiltinIdent.bvuge _              => λ x y => decide (BitVec.uge x y)
| _, BuiltinIdent.bvslt _              => λ x y => decide (BitVec.slt x y)
| _, BuiltinIdent.bvsle _              => λ x y => decide (BitVec.sle x y)
| _, BuiltinIdent.bvsgt _              => λ x y => decide (BitVec.sgt x y)
| _, BuiltinIdent.bvsge _              => λ x y => decide (BitVec.sge x y)


def denoteDefault (cs : Option ConstSort) : Type := 
   match cs with 
   | none   => Unit
   | some v => ConstSort.denote v

structure Model ( e : Env ) :=
  ( values : forall (sym : Symbol), denoteDefault (e sym) )
--   ( wfDom  : forall sym s, e.find? sym = some s -> Exists (fun v => values.findEq? sym = some v))


namespace Model

def extend {e : Env} {cs : ConstSort} (m : Model e) (k : Symbol) (v : cs.denote) 
  : Model (updMap e k cs) :=
   let pf : forall {sym} (pf : k = sym), denoteDefault ((updMap e k cs) sym) = cs.denote :=
     fun _ pf => congrArg denoteDefault (difPos pf);   
  { values := fun sym => 
           if H : k = sym then cast (pf H).symm v 
           else 
           let pf' : (updMap e k cs) sym = e sym := upd.updAtOther e (some cs) H;
           cast (congrArg denoteDefault pf'.symm)
                (m.values sym : denoteDefault (e sym))
  }

end Model

namespace SpecConst

def semantics : forall {s : SmtSort}, SpecConst s -> s.denote
  | _, binary n v => BitVec.ofNat n v

end SpecConst

instance : DecidableEq Symbol := inferInstanceAs (DecidableEq String)

namespace Ident

def semantics {e : Env} (m : Model e) : forall { cs : ConstSort } (i : Ident cs), 
              Ident.WF e i -> cs.denote
| _, symbol cs sym, wf =>
    let H : denoteDefault (e sym) = cs.denote := 
      match wf with | (Ident.WF.symbol pf) => (congrArg denoteDefault pf);
    let v : denoteDefault (e sym) := m.values sym;
    cast H v

| _, builtin i, _    => BuiltinIdent.denote _ i

end Ident

class Finite (α : Type) [DecidableEq α] :=
  (elems  : List α)
  --(complete : forall x, elems.elem x = true)



namespace SmtSort


private def denoteFinite : forall (s : SmtSort), Finite s.denote
| SmtSort.bool => {elems := [true, false]}
| SmtSort.bitvec n => {elems := List.map (BitVec.ofNat n) $ List.range (2 ^ n)}
| SmtSort.array k v =>
  let kFinite := denoteFinite k;
  let vFinite := denoteFinite v;
  let elems : List (Smt.Array k.denote v.denote):=
    vFinite.elems.joinMap $ λ (d : v.denote) =>
      kFinite.elems.powerset.joinMap $ λ (ks : List k.denote) =>
        (List.power ks vFinite.elems).map $ λ (m : List (k.denote × v.denote)) =>
          ({elems := m.qsort (λ p1 p2 => p1.fst < p2.fst), dflt := d} : Array k.denote v.denote);
  {elems := elems}


instance denote.Finite : forall (s : SmtSort), Finite s.denote :=
denoteFinite

end SmtSort

namespace Term

inductive Interp : forall (e:Env) (m:Model e) {cs:ConstSort} (t:Term cs), WF e t → cs.denote → Prop
| const : ∀ (e:Env) (m:Model e) {s : SmtSort} (sc : SpecConst s),
  Interp e m (Term.const s sc) (WF.const e sc) sc.semantics
| ident : ∀ (e:Env) (m:Model e) {cs : ConstSort} (x : Ident cs) (xWF : Ident.WF e x),
  Interp e m (Term.ident x) (WF.ident xWF) (Ident.semantics m x xWF)
| app  :  ∀ (e:Env) (m:Model e) {s : SmtSort} {cs : ConstSort} 
  (t1 : Term (ConstSort.fsort s cs))
  (wf1 : WF e t1)
  (t2 : Term (ConstSort.base s))
  (wf2 : WF e t2)
  (f : (ConstSort.fsort s cs).denote)
  (x : (ConstSort.base s).denote),
  Interp e m t1 wf1 f →
  Interp e m t2 wf2 x →
  Interp e m (Term.app t1 t2) (WF.app wf1 wf2) (f x)
| smtLet : ∀ (e:Env) (m:Model e) {s1 s2 : SmtSort} (x : Symbol)
          (t1 : Term (ConstSort.base s1))
          (wf1 : WF e t1)
          (t2 : Term (ConstSort.base s2))
          (wf2 : WF (upd e x (ConstSort.base s1)) t2)
          (v1 : (ConstSort.base s1).denote)
          (v2 : (ConstSort.base s2).denote),
  Interp e m t1 wf1 v1 →
  Interp (upd e x (ConstSort.base s1)) (m.extend x v1) t2 wf2 v2 →
  Interp e m (Term.smtLet x t1 t2) (WF.smtLet wf1 wf2) v2
| smtForallTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) (t : Term ConstSort.bool)
                  (wf : WF (updMap e x.var (ConstSort.base s)) t),
  (∀ (v : s.denote), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t wf true) →
  Interp e m (Term.smtForall x t) (WF.smtForall wf) true
| smtForallFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) (t : Term ConstSort.bool)
                  (wf : WF (updMap e x.var (ConstSort.base s)) t)
                  (witness : s.denote),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t wf false →
  Interp e m (Term.smtForall x t) (WF.smtForall wf) false
| smtExistsTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) (t : Term ConstSort.bool)
                  (wf : WF (updMap e x.var (ConstSort.base s)) t)
                  (witness : s.denote),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t wf true →
  Interp e m (Term.smtExists x t) (WF.smtExists wf) true
| smtExistsFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) (t : Term ConstSort.bool)
                  (wf : WF (updMap e x.var (ConstSort.base s)) t),
  (∀ (v : s.denote), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t wf false) →
  Interp e m (Term.smtExists x t) (WF.smtExists wf) false


end Term  


end Raw

end Smt
