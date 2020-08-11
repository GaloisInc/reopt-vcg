
import SmtLib.Syntax
import SmtLib.BitVec


namespace Smt

@[reducible]
protected def SmtSort.denote : SmtSort → Type
| SmtSort.bool => Bool
| SmtSort.bitvec n => BitVec n
| SmtSort.array k v => List (k.denote × v.denote)
-- ^ FIXME an association list would work, but obviously isn't very performant...

def SmtSort.denote.default : forall (s : SmtSort), s.denote
| SmtSort.bool => false
| SmtSort.bitvec _ => 0
| SmtSort.array _ _ => []

instance SmtSort.denote.Inhabited {s : SmtSort} : Inhabited s.denote := {default := SmtSort.denote.default s}

namespace Array

private def checkEntry {α β} [HasBeq α] (a: List (α × β) ) (k : α) (p : β → Bool) : Bool :=
match a.lookup k with 
| some v => p v
| none => false

/--  a1 == a2 iff ∀ (k,v) ∈ a1, read(a2, k) == v --/
def extensionalEq {α β} [HasBeq α] [HasBeq β]  (a1 a2 : List (α × β)) : Bool :=
a1.all (λ entry => checkEntry a2 entry.fst (λ v => v == entry.snd))
&& a2.all (λ entry => checkEntry a1 entry.fst (λ v => v == entry.snd))


def select {α β} [HasBeq α] [Inhabited β] (a: List (α × β) ) (k : α) : β :=
match a.lookup k with
| some v => v
| none => @arbitrary β _

def store {α β} [HasBeq α] [Inhabited β] (a: List (α × β)) (k : α) (v : β) : List (α × β) :=
let a' := a.filter (λ entry => entry.fst != k);
(k,v)::a'

def bvEqRange {n : Nat} {β} [HasBeq β] (a1 a2 : List (BitVec n × β)) (low high : BitVec n) : Bool :=
let inRange : BitVec n → Bool := λ bv => BitVec.ule low bv && BitVec.ule bv high;
a1.all (λ entry => !inRange entry.fst || checkEntry a2 entry.fst (λ v => v == entry.snd))
&& a2.all (λ entry => !inRange entry.fst || checkEntry a1 entry.fst (λ v => v == entry.snd))


end Array

-- FIXME / BOOKMARK ... Beq seems more flexible here and allows us to trivially not
-- care about the bitvec proofs or structure of array representation... but of course
-- we don't then get propositional equality =\
def SmtSort.denote.HasBeq : forall (s: SmtSort) , HasBeq s.denote
| SmtSort.bool =>
  {beq := λ b1 b2 => b1 == b2}
| SmtSort.bitvec n =>
  {beq := λ b1 b2 => b1 == b2}
| SmtSort.array k v =>
  {beq := @Array.extensionalEq _ _ (SmtSort.denote.HasBeq k) (SmtSort.denote.HasBeq v)}


namespace Raw

namespace ConstSort

@[reducible]
protected def denote : ConstSort → Type
| ConstSort.base s => s.denote
| ConstSort.fsort a b => a.denote → b.denote

end ConstSort

namespace VarArgs

-- private def varArgsPred (α : Type) : Nat → Type
-- | 0 => Bool
-- | Nat.succ n => α → varArgsPred n

private def distinctList {α : Type} [HasBeq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote → (nary s SmtSort.bool n).denote
| 0, args => @distinctList _ (SmtSort.denote.HasBeq s)  args
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
| _, BuiltinIdent.eq s => (SmtSort.denote.HasBeq s).beq
| _, BuiltinIdent.smtIte s => λ t x y => if t then x else y
| _, BuiltinIdent.distinct s n => mkDistinct s n

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
