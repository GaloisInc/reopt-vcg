
import Galois.Data.List
import Galois.Data.RBMap
import SmtLib.Syntax
import SmtLib.BitVec
import Std.Data.RBMap

namespace Smt

open Std (RBMap)

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


-- TODO? SpecConst

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
-- FIXME BOOKMARK check the concrete evaluator and backend over in the x86 semantics

-- -- * BitVecs
-- -- hex/binary literals
-- | _, BuiltinIdent.concat _ _           => atom "concat"
-- | _, BuiltinIdent.extract _ i j        => indexed (atom "extract") [Nat.toSExpr i, Nat.toSExpr j]
-- -- unops
-- | _, BuiltinIdent.bvnot   _            => atom "bvnot"
-- | _, BuiltinIdent.bvneg   _            => atom "bvneg"
-- -- binops                   
-- | _, BuiltinIdent.bvand   _            => atom "bvand"
-- | _, BuiltinIdent.bvor    _            => atom "bvor"
-- | _, BuiltinIdent.bvadd   _            => atom "bvadd"
-- | _, BuiltinIdent.bvmul   _            => atom "bvmul"
-- | _, BuiltinIdent.bvudiv  _            => atom "bvudiv"
-- | _, BuiltinIdent.bvurem  _            => atom "bvurem"
-- | _, BuiltinIdent.bvshl   _            => atom "bvshl"
-- | _, BuiltinIdent.bvlshr  _            => atom "bvlshr"
-- -- comparison               
-- | _, BuiltinIdent.bvult   _            => atom "bvult"

-- | _, BuiltinIdent.bvnand  _            => atom "bvnand"
-- | _, BuiltinIdent.bvnor   _            => atom "bvnor"
-- | _, BuiltinIdent.bvxor   _            => atom "bvxor"
-- | _, BuiltinIdent.bvxnor  _            => atom "bvxnor"
-- | _, BuiltinIdent.bvcomp  _            => atom "bvcomp"
-- | _, BuiltinIdent.bvsub   _            => atom "bvsub"
-- | _, BuiltinIdent.bvsdiv  _            => atom "bvsdiv"
-- | _, BuiltinIdent.bvsrem  _            => atom "bvsrem"
-- | _, BuiltinIdent.bvsmod  _            => atom "bvsmod"
-- | _, BuiltinIdent.bvashr  _            => atom "bvashr"

-- | _, BuiltinIdent.repeat i _           => indexed (atom "repeat") [Nat.toSExpr i]

-- | _, BuiltinIdent.zeroExtend  i _     => indexed (atom "zero_extend")  [Nat.toSExpr i]
-- | _, BuiltinIdent.signExtend  i _     => indexed (atom "sign_extend")  [Nat.toSExpr i]
-- | _, BuiltinIdent.rotateLeft  i _     => indexed (atom "rotate_left")  [Nat.toSExpr i]
-- | _, BuiltinIdent.rotateRight i _     => indexed (atom "rotate_right") [Nat.toSExpr i]

-- | _, BuiltinIdent.bvule _              => atom "bvule"
-- | _, BuiltinIdent.bvugt _              => atom "bvugt"
-- | _, BuiltinIdent.bvuge _              => atom "bvuge"
-- | _, BuiltinIdent.bvslt _              => atom "bvslt"
-- | _, BuiltinIdent.bvsle _              => atom "bvsle"
-- | _, BuiltinIdent.bvsgt _              => atom "bvsgt"
-- | _, BuiltinIdent.bvsge _              => atom "bvsge"
| cs, _                    => "TODO"


end Raw

end Smt
