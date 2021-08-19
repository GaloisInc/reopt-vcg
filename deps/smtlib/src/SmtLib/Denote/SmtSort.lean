/-
Denotation from SMT sorts to Lean types.

Copyright (c) 2020 Galois Inc. All rights reserved.
-/

import Galois.Data.Bitvec
import Galois.Data.List
import Galois.Init.Order
import SmtLib.Denote.Array
import SmtLib.Syntax


namespace Smt


------------------------------------------------------------
-- Bool (ordering and class instances)

namespace Bool

protected
inductive LT : Bool → Bool → Prop
| lt : Bool.LT true false

private def lessLeftTrue : forall {b1 b2 : Bool}, Bool.LT b1 b2 → b1 = true
| true, _, _ => rfl

private def lessRightFalse : forall {b1 b2 : Bool}, Bool.LT b1 b2 → b2 = false
| _, false, _ => rfl


private def boolDecidableLT (x y : Bool) : Decidable (Bool.LT x y) :=
@Bool.casesOn
  (λ b => Decidable (Bool.LT b y))
  x
  (isFalse (λ (h : Bool.LT false y) => Bool.noConfusion (lessLeftTrue h)))
  (@Bool.casesOn
    (λ b => Decidable (Bool.LT true b))
    y
    (isTrue Bool.LT.lt)
    (isFalse (λ (h : Bool.LT true true) => Bool.noConfusion (lessRightFalse h))))


instance : LT Bool := ⟨Bool.LT⟩
instance : DecidableLT Bool := boolDecidableLT

axiom LT.transitivity :∀ (x y z : Bool), x < y → y < z → x < z
axiom LT.asymmetry : ∀ (x y : Bool), x < y → ¬(y < x)
axiom LT.totality : ∀ (x y : Bool), x < y ∨ x = y ∨ y < x

instance : LTOrder Bool :=
{transitive := LT.transitivity,
 asymmetric := LT.asymmetry,
 total := LT.totality}


instance : DecidableLTOrder Bool :=
  { ltDec := boolDecidableLT
  , eqDec := inferInstance
  }

end Bool

------------------------------------------------------------
-- bitvec (ordering and class instances)


namespace bitvec

protected
def LT {n : Nat} : bitvec n → bitvec n → Prop := bitvec.ult

instance less (n:Nat) : LT (bitvec n) := ⟨bitvec.LT⟩
instance decidableLT (n:Nat) : DecidableLT (bitvec n) := @bitvec.decidable_ult n

axiom LT.transitivity {n} : ∀ (x y z : bitvec n), x < y → y < z → x < z
axiom LT.asymmetry {n} : ∀ (x y : bitvec n), x < y → ¬(y < x)
axiom LT.totality {n} : ∀ (x y : bitvec n), x < y ∨ x = y ∨ y < x

instance {n} : LTOrder (bitvec n) :=
{transitive := LT.transitivity,
 asymmetric := LT.asymmetry,
 total := LT.totality}


instance {n} : DecidableLTOrder (bitvec n) :=
{ltDec := decidableLT n,
 eqDec := @bitvec_DecidableEq n}

end bitvec

------------------------------------------------------------
-- Prod (ordering and class instances)

namespace Prod

axiom LT.transitivity {a b} [LTOrder a] [LTOrder b] : ∀ (x y z : a × b), x < y → y < z → x < z
axiom LT.asymmetry {a b} [LTOrder a] [LTOrder b] : ∀ (x y : a × b), x < y → ¬(y < x)
axiom LT.totality {a b} [LTOrder a] [LTOrder b] : ∀ (x y : a × b), x < y ∨ x = y ∨ y < x

instance {a b} [LTOrder a] [LTOrder b] : LTOrder (a × b) :=
{transitive := LT.transitivity,
 asymmetric := LT.asymmetry,
 total := LT.totality}

instance {a b} [DecidableLTOrder a] [DecidableLTOrder b] : DecidableLTOrder (a × b) :=
{ltDec := inferInstance,
 eqDec := inferInstance}

end Prod



------------------------------------------------------------
-- SMT sort denotations and instances


/-- A type and a corresponding decidable total ordering. -/
structure OrderedType :=
(type : Type)
(order : DecidableLTOrder type)


/--  Denotation of SMT sorts. -/
@[reducible]
def denoteSmtSort : SmtSort → OrderedType
| SmtSort.bool => ⟨Bool, inferInstance⟩
| SmtSort.bitvec n => ⟨bitvec n, inferInstance⟩
| SmtSort.array k v =>
  let k' := denoteSmtSort k;
  let kOrd := k'.order;
  let v' := denoteSmtSort v;
  let vOrd := v'.order;
  ⟨Array k'.type v'.type, inferInstance⟩
| SmtSort.tuple a b =>
  let a' := denoteSmtSort a;
  let aOrd := a'.order;
  let b' := denoteSmtSort b;
  let bOrd := b'.order;
  ⟨a'.type × b'.type, inferInstance⟩


@[reducible]
def SmtSort.denote (s : SmtSort) : OrderedType := denoteSmtSort s

instance SmtSort.denote.LT : ∀ (s:SmtSort), LT s.denote.type
| s => ⟨s.denote.order.lt⟩


instance SmtSort.denote.DecidableLT : ∀ (s:SmtSort), DecidableLT s.denote.type
| s => s.denote.order.ltDec


instance SmtSort.denote.DecidableEq : ∀ (s:SmtSort), DecidableEq s.denote.type
| s => s.denote.order.eqDec


instance SmtSort.denote.DecidableLTOrder : ∀ (s:SmtSort), DecidableLTOrder s.denote.type
| s => s.denote.order

end Smt
