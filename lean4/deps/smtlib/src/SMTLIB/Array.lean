
import Galois.Data.List

namespace Smt
universes u v

structure FiniteMap (α : Type u) (β : Type v) : Type (max u v) :=
(entries : List (α × β))
(default : β)

namespace FiniteMap

section
variables {α : Type u} {β : Type v}

def FiniteMap.decEq
  [DecidableEq α]
  [DecidableEq β]
  (fm1 fm2 : FiniteMap α β) : Decidable (fm1 = fm2) :=
FiniteMap.casesOn fm1 $ λ es1 d1 => FiniteMap.casesOn fm2 $ λ es2 d2 =>
  match (decEq es1 es2) with
  | (isTrue e₁) =>
    match (decEq d1 d2) with
    | (isTrue e₂)  => isTrue (Eq.recOn e₁ (Eq.recOn e₂ rfl))
    | (isFalse n₂) => isFalse (fun h => FiniteMap.noConfusion h (fun e₁' e₂' => absurd e₂' n₂))
  | (isFalse n₁) => isFalse (fun h => FiniteMap.noConfusion h (fun e₁' e₂' => absurd e₁' n₁))


instance [DecidableEq α] [DecidableEq β] : DecidableEq (FiniteMap α β) :=
FiniteMap.decEq

section
variables [HasLess α] [HasLess β]

def FiniteMap.Less : FiniteMap α β → FiniteMap α β → Prop
| a1, a2 => (a1.entries, a1.default) < (a2.entries, a2.default)

instance FiniteMap.HasLess : HasLess (FiniteMap α β) :=
⟨@FiniteMap.Less α β _ _ _ _⟩


def FiniteMap.decLt
  [DecidableLess α]
  [DecidableLess β]
  (fm1 fm2 : FiniteMap α β) : Decidable (fm1 < fm2) :=
FiniteMap.casesOn fm1 $ λ es1 d1 => FiniteMap.casesOn fm2 $ λ es2 d2 =>
  let prodLtDec : ∀ (p1 p2 : (α × β)), Decidable (p1 < p2) := prodHasDecidableLt;
  let listLtDec : ∀ (l1 l2 : List (α × β)), Decidable (l1 < l2) := List.hasDecidableLt;
  inferInstanceAs (Decidable ((es1, d1) < (es2, d2)))


instance FiniteMap.DecidableLess
  [DecidableLess α]
  [DecidableLess β] : ∀ (x y : FiniteMap α β), Decidable (x < y) :=
FiniteMap.decLt


end

end

axiom LessTransitivity {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y z : α), x < y → y < z → x < z) →
(∀ (x y z : β), x < y → y < z → x < z) →
(∀ (x y z : FiniteMap α β), x < y → y < z → x < z)

axiom LessAsymmetry {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y : α), x < y → ¬(y < x)) →
(∀ (x y : β), x < y → ¬(y < x)) →
(∀ (x y : FiniteMap α β), x < y → ¬(y < x))

axiom LessTotality {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y : α), x < y ∨ x = y ∨ y < x) →
(∀ (x y : β), x < y ∨ x = y ∨ y < x) →
(∀ (x y : FiniteMap α β), x < y ∨ x = y ∨ y < x)

instance {α : Type u} {β : Type v} [HasLessOrder α] [HasLessOrder β] : HasLessOrder (FiniteMap α β) :=
{ transitive := FiniteMap.LessTransitivity,
  assymetric := FiniteMap.LessAsymmetry,
  total := FiniteMap.LessTotality
}

end FiniteMap


def Array (α : Type u) (β : Type v)
  [DecidableLessOrder α]
  [DecidableLessOrder β] : Type (max u v) :=
{ model : FiniteMap α β
  // model.entries.IsSortedAList
    ∧ model.entries.Forall (λ (kv : α × β) => kv.snd ≠ model.default)
}

namespace Array
variables {α : Type u} {β : Type v}

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : DecidableEq (Array α β) :=
Subtype.DecidableEq

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : HasLess (Array α β) :=
Subtype.HasLess

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : DecidableLess (Array α β) :=
Subtype.DecidableLess

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : HasLessOrder (Array α β) :=
Subtype.DecidableLess -- BOOKMARK

--axiom 

end Array


end Smt
