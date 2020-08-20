
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
protected def SmtSort.carrier : SmtSort → Type
| SmtSort.bool => Bool
| SmtSort.bitvec n => BitVec n
| SmtSort.array k v => Array k.carrier v.carrier



-- protected def SmtSort.denote : Nat → SmtSort → Type
-- | idx, s => (s.denotation idx).fst



-- def SmtSort.carrier.HasBeq : forall (s: SmtSort) , HasBeq s.carrier
-- | SmtSort.bool =>
--   {beq := λ b1 b2 => b1 == b2}
-- | SmtSort.bitvec n =>
--   {beq := λ b1 b2 => b1 == b2}
-- | SmtSort.array k v =>
--   let beqK := SmtSort.carrier.HasBeq k;
--   let beqV := SmtSort.carrier.HasBeq v;
--   {beq := λ a1 a2 => a1.dflt == a2.dflt && a1.elems  == a2.elems}



namespace SmtSort

inductive BoolLess : Bool → Bool → Prop
| trueLess (b : Bool) : BoolLess true b

private def carrierHasLess : forall (s: SmtSort) , HasLess s.carrier
| SmtSort.bool => {Less := BoolLess}
| SmtSort.bitvec n => {Less := @BitVec.ult n}
| SmtSort.array k v =>
  let kHasLess := carrierHasLess k;
  let vHasLess := carrierHasLess v;
  Array.HasLess


instance carrier.HasLess : forall (s : SmtSort), HasLess s.carrier := 
carrierHasLess


-- private def carrierDedicableEq : forall (s : SmtSort), DecidableEq s.carrier :=

-- instance carrier.DecidableEq : forall (s : SmtSort), DecidableEq s.carrier :=
-- carrierDecidableEq


end SmtSort

namespace Raw

namespace ConstSort

@[reducible]
protected def carrier : ConstSort → Type
| ConstSort.base s => s.carrier
| ConstSort.fsort a b => a.carrier → b.carrier

end ConstSort

namespace VarArgs

-- private def varArgsPred (α : Type) : Nat → Type
-- | 0 => Bool
-- | Nat.succ n => α → varArgsPred n

private def distinctList {α : Type} [HasBeq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


-- FIXME
-- def distinct (s : SmtSort) : forall (n : Nat), List s.carrier → (nary s SmtSort.bool n).carrier
-- | 0, args => @distinctList _ (SmtSort.carrier.HasBeq s)  args
-- | Nat.succ n, args => λ a => (distinct n) (a::args)

end VarArgs

-- FIXME
-- private def mkDistinct (s : SmtSort) (n : Nat) : (nary s SmtSort.bool n).carrier :=
-- VarArgs.distinct s n []



namespace Array
variables {α β : Type} {lt : α → α → Bool}

protected def toList (a : Array α β) : List (α × β) :=
a.elems

protected def keys (a : Array α β) : List α :=
a.elems.map (λ e => e.fst)



protected def select [HasBeq α] (a : Array α β) (k : α) : β :=
match a.elems.lookup k with
| some v => v
| none => a.dflt


protected def store (a : Array α β) (lt : α → α → Bool) (k : α) (v : β) : Array α β :=
{a with elems := SortedAList.insert lt k v a.elems}

-- def lexLt (a1 a2 : Array α β lt dflt) : Bool :=
-- List.lexLt lt a1.keys a2.keys

-- private def checkEntry (a : Array α β lt dflt) (k : α) (p : β → Bool) : Bool :=
-- match a.elems.find? k with
-- | some v => p v
-- | none => false

-- /--  a1 == a2 iff ∀ (k,v) ∈ a1, read(a2, k) == v --/
-- def extensionalEq (eq : β → β → Bool)  (a1 a2 : Array α β lt dflt) : Bool :=
-- a1.toList.all (λ entry => checkEntry a2 entry.fst (eq entry.snd))
-- && a2.toList.all (λ entry => checkEntry a1 entry.fst (eq entry.snd))


-- def eqRange (eq : β → β → Bool) (a1 a2 : Array α β lt dflt) (low high : α) : Bool :=
-- let inRange : α → Bool := λ k => !(lt k low) && !(lt high k);
-- a1.toList.all (λ entry => !inRange entry.fst || checkEntry a2 entry.fst (eq entry.snd))
-- && a2.toList.all (λ entry => !inRange entry.fst || checkEntry a1 entry.fst (eq entry.snd))


end Array


-- TODO? SpecConst

@[reducible]
protected def BuiltinIdent.carrier : forall cs, BuiltinIdent cs → cs.carrier
-- * Core theory
| _, BuiltinIdent.true => true
| _, BuiltinIdent.false => false
| _, BuiltinIdent.not => not
| _, BuiltinIdent.impl => λ p q => !p || q
| _, BuiltinIdent.and => and
| _, BuiltinIdent.or => or
| _, BuiltinIdent.xor => xor
| _, BuiltinIdent.eq s => (SmtSort.carrier.HasBeq s).beq
| _, BuiltinIdent.smtIte s => λ t x y => if t then x else y
--| _, BuiltinIdent.distinct s n => mkDistinct s n -- FIXME

-- | _, select _ _           => atom "select"
-- | _, store  _ _           => atom "store"
-- | _, eqrange _ _          => atom "eqrange"

-- -- * BitVecs
-- -- hex/binary literals
-- | _, concat _ _           => atom "concat"
-- | _, extract _ i j        => indexed (atom "extract") [Nat.toSExpr i, Nat.toSExpr j]
-- -- unops
-- | _, bvnot   _            => atom "bvnot"
-- | _, bvneg   _            => atom "bvneg"
-- -- binops                   
-- | _, bvand   _            => atom "bvand"
-- | _, bvor    _            => atom "bvor"
-- | _, bvadd   _            => atom "bvadd"
-- | _, bvmul   _            => atom "bvmul"
-- | _, bvudiv  _            => atom "bvudiv"
-- | _, bvurem  _            => atom "bvurem"
-- | _, bvshl   _            => atom "bvshl"
-- | _, bvlshr  _            => atom "bvlshr"
-- -- comparison               
-- | _, bvult   _            => atom "bvult"

-- | _, bvnand  _            => atom "bvnand" 
-- | _, bvnor   _            => atom "bvnor" 
-- | _, bvxor   _            => atom "bvxor"  
-- | _, bvxnor  _            => atom "bvxnor"  
-- | _, bvcomp  _            => atom "bvcomp" 
-- | _, bvsub   _            => atom "bvsub" 
-- | _, bvsdiv  _            => atom "bvsdiv"
-- | _, bvsrem  _            => atom "bvsrem" 
-- | _, bvsmod  _            => atom "bvsmod" 
-- | _, bvashr  _            => atom "bvashr" 

-- | _, repeat i _           => indexed (atom "repeat") [Nat.toSExpr i]

-- | _, zeroExtend  i _     => indexed (atom "zero_extend")  [Nat.toSExpr i]
-- | _, signExtend  i _     => indexed (atom "sign_extend")  [Nat.toSExpr i]
-- | _, rotateLeft  i _     => indexed (atom "rotate_left")  [Nat.toSExpr i]
-- | _, rotateRight i _     => indexed (atom "rotate_right") [Nat.toSExpr i]

-- | _, bvule _              => atom "bvule" 
-- | _, bvugt _              => atom "bvugt" 
-- | _, bvuge _              => atom "bvuge" 
-- | _, bvslt _              => atom "bvslt" 
-- | _, bvsle _              => atom "bvsle" 
-- | _, bvsgt _              => atom "bvsgt" 
-- | _, bvsge _              => atom "bvsge" 
| cs, _                    => "TODO"


end Raw

end Smt
