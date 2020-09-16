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

inductive Less : Bool → Bool → Prop
| lt : Less true false

private def lessLeftTrue : forall {b1 b2 : Bool}, Less b1 b2 → b1 = true
| true, _, _ => rfl

private def lessRightFalse : forall {b1 b2 : Bool}, Less b1 b2 → b2 = false
| _, false, _ => rfl


private def boolDecidableLt (x y : Bool) : Decidable (Less x y) :=
@Bool.casesOn
  (λ b => Decidable (Less b y))
  x
  (isFalse (λ (h : Less false y) => Bool.noConfusion (lessLeftTrue h)))
  (@Bool.casesOn
    (λ b => Decidable (Less true b))
    y
    (isTrue Less.lt)
    (isFalse (λ (h : Less true true) => Bool.noConfusion (lessRightFalse h))))


instance : HasLess Bool := ⟨Less⟩
instance : DecidableLess Bool := boolDecidableLt

axiom Less.transitivity :∀ (x y z : Bool), x < y → y < z → x < z
axiom Less.asymmetry : ∀ (x y : Bool), x < y → ¬(y < x)
axiom Less.totality : ∀ (x y : Bool), x < y ∨ x = y ∨ y < x

instance : HasLessOrder Bool :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance : DecidableLessOrder Bool :=
{ltDec := Bool.DecidableLess,
 eqDec := Bool.DecidableEq}

end Bool

------------------------------------------------------------
-- bitvec (ordering and class instances)


namespace bitvec

def Less {n : Nat} : bitvec n → bitvec n → Prop := bitvec.ult

instance (n:Nat) : HasLess (bitvec n) := ⟨bitvec.Less⟩
instance (n:Nat) : DecidableLess (bitvec n) := @bitvec.decidable_ult n 

axiom Less.transitivity {n} : ∀ (x y z : bitvec n), x < y → y < z → x < z
axiom Less.asymmetry {n} : ∀ (x y : bitvec n), x < y → ¬(y < x)
axiom Less.totality {n} : ∀ (x y : bitvec n), x < y ∨ x = y ∨ y < x

instance {n} : HasLessOrder (bitvec n) :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance {n} : DecidableLessOrder (bitvec n) :=
{ltDec := @bitvec.DecidableLess n,
 eqDec := @bitvec_DecidableEq n}

end bitvec



------------------------------------------------------------
-- SMT sort denotations and instances


/-- A type and a corresponding decidable total ordering. -/
structure OrderedType :=
(type : Type)
(order : DecidableLessOrder type)


/--  Denotation of SMT sorts. -/
@[reducible]
protected def SmtSort.denote : SmtSort → OrderedType
| SmtSort.bool => ⟨Bool, Bool.DecidableLessOrder⟩
| SmtSort.bitvec n => ⟨bitvec n, bitvec.DecidableLessOrder⟩
| SmtSort.array k v =>
  let k' := k.denote;
  let kOrd := k'.order;
  let v' := v.denote;
  let vOrd := v'.order;
  ⟨Array k'.type v'.type, Array.DecidableLessOrder⟩


instance SmtSort.denote.HasLess : ∀ (s:SmtSort), HasLess s.denote.type
| s => ⟨s.denote.order.Less⟩


instance SmtSort.denote.DecidableLess : ∀ (s:SmtSort), DecidableLess s.denote.type
| s => s.denote.order.ltDec


instance SmtSort.denote.DecidableEq : ∀ (s:SmtSort), DecidableEq s.denote.type
| s => s.denote.order.eqDec


instance SmtSort.denote.DecidableLessOrder : ∀ (s:SmtSort), DecidableLessOrder s.denote.type
| s => s.denote.order

end Smt