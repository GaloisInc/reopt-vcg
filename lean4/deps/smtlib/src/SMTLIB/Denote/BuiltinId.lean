/-
Denotations for SMT builtin functions.

Copyright (c) 2020 Galois Inc. All rights reserved.
-/

import SmtLib.Denote.SmtSort
import SmtLib.Syntax

namespace Smt

namespace Array
section
variables {α β : Type} [DecidableLessOrder α] [DecidableLessOrder β]


private def bvEqRangeAux {n} (a1 a2 : Array (BitVec n) β) (low : BitVec n) : Nat → Bool
| Nat.zero => a1.select 0 == a2.select 0
| Nat.succ i =>
  let idx := low + (BitVec.ofNat n i) + 1;
  a1.select idx == a2.select idx && bvEqRangeAux i

end

section
variables {β : Type} [DecidableLessOrder β]


def bvEqRange {n} (a1 a2 : Array (BitVec n) β) (low high : BitVec n) : Bool :=
if high < low then true
else
  let rangeSize := high - low;
  bvEqRangeAux a1 a2 low rangeSize.toNat


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
| ConstSort.fsort a b => a.denote.type → (denote b)

end ConstSort

namespace VarArgs

private def varArgsPred (α : Type) : Nat → Type
| 0 => Bool
| Nat.succ n => α → varArgsPred n


private def distinctList {α : Type} [DecidableEq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote.type → (nary s SmtSort.bool n).denote
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

| _, BuiltinIdent.select k v           => Array.select
| _, BuiltinIdent.store  k v           => Array.store
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


end Raw

end Smt
