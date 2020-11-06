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
inductive Less : Bool → Bool → Prop
| lt : Bool.Less true false

private def lessLeftTrue : forall {b1 b2 : Bool}, Bool.Less b1 b2 → b1 = true
| true, _, _ => rfl

private def lessRightFalse : forall {b1 b2 : Bool}, Bool.Less b1 b2 → b2 = false
| _, false, _ => rfl


private def boolDecidableLt (x y : Bool) : Decidable (Bool.Less x y) :=
@Bool.casesOn
  (λ b => Decidable (Bool.Less b y))
  x
  (isFalse (λ (h : Bool.Less false y) => Bool.noConfusion (lessLeftTrue h)))
  (@Bool.casesOn
    (λ b => Decidable (Bool.Less true b))
    y
    (isTrue Bool.Less.lt)
    (isFalse (λ (h : Bool.Less true true) => Bool.noConfusion (lessRightFalse h))))


instance : Less Bool := ⟨Bool.Less⟩
instance : DecidableLess Bool := boolDecidableLt

axiom Less.transitivity :∀ (x y z : Bool), x < y → y < z → x < z
axiom Less.asymmetry : ∀ (x y : Bool), x < y → ¬(y < x)
axiom Less.totality : ∀ (x y : Bool), x < y ∨ x = y ∨ y < x

instance : LessOrder Bool :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance : DecidableLessOrder Bool :=
  { ltDec := boolDecidableLt
  , eqDec := inferInstance
  }

end Bool

------------------------------------------------------------
-- bitvec (ordering and class instances)


namespace bitvec

protected
def Less {n : Nat} : bitvec n → bitvec n → Prop := bitvec.ult

instance less (n:Nat) : Less (bitvec n) := ⟨bitvec.Less⟩
instance decidableLess (n:Nat) : DecidableLess (bitvec n) := @bitvec.decidable_ult n 

axiom Less.transitivity {n} : ∀ (x y z : bitvec n), x < y → y < z → x < z
axiom Less.asymmetry {n} : ∀ (x y : bitvec n), x < y → ¬(y < x)
axiom Less.totality {n} : ∀ (x y : bitvec n), x < y ∨ x = y ∨ y < x

instance {n} : LessOrder (bitvec n) :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance {n} : DecidableLessOrder (bitvec n) :=
{ltDec := decidableLess n,
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
def denoteSmtSort : SmtSort → OrderedType
| SmtSort.bool => ⟨Bool, inferInstance⟩
| SmtSort.bitvec n => ⟨bitvec n, inferInstance⟩
| SmtSort.array k v =>
  let k' := denoteSmtSort k;
  let kOrd := k'.order;
  let v' := denoteSmtSort v;
  let vOrd := v'.order;
  ⟨Array k'.type v'.type, inferInstance⟩


@[reducible]
def SmtSort.denote (s : SmtSort) : OrderedType := denoteSmtSort s

instance SmtSort.denote.HasLess : ∀ (s:SmtSort), Less s.denote.type
| s => ⟨s.denote.order.Less⟩


instance SmtSort.denote.DecidableLess : ∀ (s:SmtSort), DecidableLess s.denote.type
| s => s.denote.order.ltDec


instance SmtSort.denote.DecidableEq : ∀ (s:SmtSort), DecidableEq s.denote.type
| s => s.denote.order.eqDec


instance SmtSort.denote.DecidableLessOrder : ∀ (s:SmtSort), DecidableLessOrder s.denote.type
| s => s.denote.order

end Smt
