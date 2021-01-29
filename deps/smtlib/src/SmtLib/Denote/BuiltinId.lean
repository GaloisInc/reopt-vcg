/-
Denotations for SMT builtin functions.

Copyright (c) 2020 Galois Inc. All rights reserved.
-/

import Galois.Data.Bitvec
import SmtLib.Denote.SmtSort
import SmtLib.Syntax

namespace Smt

namespace Array
section
variable {α β : Type} [DecidableLessOrder α] [DecidableLessOrder β]


private def bvEqRangeAux {n} (a1 a2 : Array (bitvec n) β) (low : bitvec n) : Nat → Bool
| Nat.zero => a1.select 0 == a2.select 0
| Nat.succ i =>
  let idx := low + (bitvec.of_nat n i) + 1;
  a1.select idx == a2.select idx && bvEqRangeAux a1 a2 low i

end

section
variable {β : Type} [DecidableLessOrder β]


def bvEqRange {n} (a1 a2 : Array (bitvec n) β) (low high : bitvec n) : Bool :=
if high < low then true
else
  let rangeSize := high - low;
  bvEqRangeAux a1 a2 low rangeSize.to_nat


def eqRange :
  forall (k : RangeSort),
  Array k.sort.denote.type β →
  Array k.sort.denote.type β →
  k.sort.denote.type →
  k.sort.denote.type → Bool
| RangeSort.bitvec n, a1, a2, low, high => bvEqRange a1 a2 low high


end

end Array


namespace Raw

namespace ConstSort

@[reducible]
protected def denote : ConstSort → Type
| ConstSort.base s => s.denote.type
| ConstSort.fsort a b => a.denote.type → (ConstSort.denote b)

end ConstSort

namespace VarArgs

private def varArgsPred (α : Type) : Nat → Type
| 0 => Bool
| Nat.succ n => α → varArgsPred α n


private def distinctList {α : Type} [DecidableEq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote.type → (nary s SmtSort.bool n).denote
| 0, args => distinctList args
| Nat.succ n, args => λ a => (distinct s n) (a::args)

end VarArgs


private def mkDistinct (s : SmtSort) (n : Nat) : (nary s SmtSort.bool n).denote :=
VarArgs.distinct s n []


@[reducible]
def denoteBuiltinIdent : forall cs, BuiltinIdent cs → cs.denote
-- * Core theory
| _, BuiltinIdent.true => true
| _, BuiltinIdent.false => false
| _, BuiltinIdent.not => not
| _, BuiltinIdent.impl => λ p q => !p || q
| _, BuiltinIdent.and => and
| _, BuiltinIdent.or => or
| _, BuiltinIdent.xor => λ p q => not (p == q)
| _, BuiltinIdent.eq s => λ x y => BEq.beq x y
| _, BuiltinIdent.smtIte s => λ t x y =>
                                match t with
                                | true =>  x 
                                | false => y
| _, BuiltinIdent.distinct s n => mkDistinct s n

| _, BuiltinIdent.select k v           => Array.select
| _, BuiltinIdent.store  k v           => Array.store
| _, BuiltinIdent.eqrange k _          => Array.eqRange k

-- -- * bitvecs
-- -- hex/binary literals
| _, BuiltinIdent.concat _ _           => bitvec.append
| _, BuiltinIdent.extract n i j        => bitvec.extract i j
-- -- unops
| _, BuiltinIdent.bvnot   _            => bitvec.not
| _, BuiltinIdent.bvneg   _            => bitvec.neg
-- -- binops                   
| _, BuiltinIdent.bvand   _            => bitvec.and
| _, BuiltinIdent.bvor    _            => bitvec.or
| _, BuiltinIdent.bvadd   _            => bitvec.add
| _, BuiltinIdent.bvmul   _            => bitvec.mul
| _, BuiltinIdent.bvudiv  _            => bitvec.udiv
| _, BuiltinIdent.bvurem  _            => bitvec.urem
| _, BuiltinIdent.bvshl   _            => λ b i => bitvec.shl b i.to_nat
| _, BuiltinIdent.bvlshr  _            => λ b i => bitvec.ushr b i.to_nat
-- -- comparison               
| _, BuiltinIdent.bvult   _            => λ b1 b2 => decide (bitvec.ult b1 b2)

| _, BuiltinIdent.bvnand  _            => λ b1 b2 => bitvec.not (bitvec.and b1 b2)
| _, BuiltinIdent.bvnor   _            => λ b1 b2 => bitvec.not (bitvec.or b1 b2)
| _, BuiltinIdent.bvxor   _            => bitvec.xor
| _, BuiltinIdent.bvxnor  _            => λ b1 b2 => bitvec.not (bitvec.xor b1 b2)
| _, BuiltinIdent.bvcomp  _            => λ b1 b2 => if b1 = b2 then bitvec.of_nat _ 1 else bitvec.of_nat _ 0
| _, BuiltinIdent.bvsub   _            => bitvec.sub
| _, BuiltinIdent.bvsdiv  _            => bitvec.sdiv
| _, BuiltinIdent.bvsrem  _            => bitvec.srem
| _, BuiltinIdent.bvsmod  _            => bitvec.smod
| _, BuiltinIdent.bvashr  _            => λ b i => bitvec.sshr b i.to_nat

| _, BuiltinIdent.repeat i _           => λ b => bitvec.repeat b i

| _, BuiltinIdent.zeroExtend  i n     => λ b => b.uresize (n + i)
| _, BuiltinIdent.signExtend  i n     => λ b => b.sresize (n + i)
| _, BuiltinIdent.rotateLeft  i _     => bitvec.rotateLeft i
| _, BuiltinIdent.rotateRight i _     => bitvec.rotateRight i

| _, BuiltinIdent.bvule _              => λ x y => decide (bitvec.ule x y)
| _, BuiltinIdent.bvugt _              => λ x y => decide (bitvec.ugt x y)
| _, BuiltinIdent.bvuge _              => λ x y => decide (bitvec.uge x y)
| _, BuiltinIdent.bvslt _              => λ x y => decide (bitvec.slt x y)
| _, BuiltinIdent.bvsle _              => λ x y => decide (bitvec.sle x y)
| _, BuiltinIdent.bvsgt _              => λ x y => decide (bitvec.sgt x y)
| _, BuiltinIdent.bvsge _              => λ x y => decide (bitvec.sge x y)

def BuiltinIdent.denote : forall cs, BuiltinIdent cs → cs.denote := denoteBuiltinIdent

end Raw

end Smt
