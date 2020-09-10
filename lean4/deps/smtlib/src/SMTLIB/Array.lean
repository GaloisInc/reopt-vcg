
import Galois.Data.List
import Galois.Init.Order

namespace Smt
universes u v

structure FiniteMap (α : Type u) (β : Type v) : Type (max u v) :=
(entries : List (α × β))
(default : β)

namespace FiniteMap

def empty (α : Type u) {β : Type v} (default : β) : FiniteMap α β :=
⟨[], default⟩

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
⟨@FiniteMap.Less α β _ _⟩


def FiniteMap.decLt
  [DecidableEq α]
  [DecidableEq β]
  [DecidableLess α]
  [DecidableLess β]
  (fm1 fm2 : FiniteMap α β)
  : Decidable (fm1 < fm2) :=
FiniteMap.casesOn fm1 $ λ es1 d1 => FiniteMap.casesOn fm2 $ λ es2 d2 =>
  let prodLtDec : ∀ (p1 p2 : (α × β)), Decidable (p1 < p2) := prodHasDecidableLt;
  let listLtDec : ∀ (l1 l2 : List (α × β)), Decidable (l1 < l2) := List.hasDecidableLt;
  inferInstanceAs (Decidable ((es1, d1) < (es2, d2)))


instance FiniteMap.DecidableLess
  [DecidableEq α]
  [DecidableEq β]
  [DecidableLess α]
  [DecidableLess β]
  : ∀ (x y : FiniteMap α β), Decidable (x < y) :=
FiniteMap.decLt


end

end

axiom Less.transitivity {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y z : α), x < y → y < z → x < z) →
(∀ (x y z : β), x < y → y < z → x < z) →
(∀ (x y z : FiniteMap α β), x < y → y < z → x < z)

axiom Less.asymmetry {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y : α), x < y → ¬(y < x)) →
(∀ (x y : β), x < y → ¬(y < x)) →
(∀ (x y : FiniteMap α β), x < y → ¬(y < x))

axiom Less.totality {α : Type u} {β : Type v}
 [HasLess α] [HasLess β]
 [DecidableEq α] [DecidableEq β] :
(∀ (x y : α), x < y ∨ x = y ∨ y < x) →
(∀ (x y : β), x < y ∨ x = y ∨ y < x) →
(∀ (x y : FiniteMap α β), x < y ∨ x = y ∨ y < x)

instance {α : Type u} {β : Type v}
  [DecidableEq α] [DecidableEq β]
  [hA : HasLessOrder α] [hB : HasLessOrder β]
  : HasLessOrder (FiniteMap α β) :=
{ transitive := FiniteMap.Less.transitivity hA.transitive hB.transitive,
  asymmetric := FiniteMap.Less.asymmetry hA.asymmetric hB.asymmetric,
  total := FiniteMap.Less.totality hA.total hB.total
}

structure WellFormed {α : Type u} {β : Type v} (fm : FiniteMap α β)
  [DecidableLessOrder α]
  [DecidableLessOrder β] : Prop :=
(sorted : fm.entries.IsSortedMap)
(noDefault : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default))

def empty.wellFormed (α : Type u) {β : Type v}
  [DecidableLessOrder α]
  [DecidableLessOrder β]
  (v : β) : FiniteMap.WellFormed (FiniteMap.empty α v) :=
⟨List.IsSortedMap.nil, List.Forall.nil⟩

end FiniteMap

def Array (α : Type u) (β : Type v)
  [DecidableLessOrder α]
  [DecidableLessOrder β] : Type (max u v) :=
{ fm : FiniteMap α β // FiniteMap.WellFormed fm}

namespace Array
variables {α : Type u} {β : Type v}

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : DecidableEq (Array α β) :=
Subtype.DecidableEq

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : HasLess (Array α β) :=
Subtype.HasLess

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : DecidableLess (Array α β) :=
Subtype.DecidableLess

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : HasLessOrder (Array α β) :=
Subtype.HasLessOrder

instance [hA : DecidableLessOrder α] [hB : DecidableLessOrder β] : DecidableLessOrder (Array α β) :=
{ eqDec := Array.DecidableEq,
  ltDec := Array.DecidableLess
}


--def const

section Operations
variables [DecidableLessOrder α] [DecidableLessOrder β]

def select (a : Array α β) (k : α) : β :=
match a.val.entries.lookup k with
| some v => v
| none => a.val.default


def store (a : Array α β) (k : α) (v : β) : Array α β :=
if h : v = a.val.default
then
  let fm : FiniteMap α β := {a.val with entries := List.SortedMap.erase k a.val.entries};
  have h1 : fm.entries.IsSortedMap from
    List.SortedMap.erase.wellFormed k a.property.sorted;
  have h2 : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default) from
    List.SortedMap.erase.stillNotIn k a.property.noDefault;
  ⟨fm, ⟨h1, h2⟩⟩
else
  let fm : FiniteMap α β := {a.val with entries := List.SortedMap.insert k v a.val.entries};
  have h1 : fm.entries.IsSortedMap from
    List.SortedMap.insert.wellFormed k v a.property.sorted;
  have h2 : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default) from
    List.SortedMap.insert.stillNotIn k h a.property.noDefault;
  ⟨fm, ⟨h1, h2⟩⟩

end Operations

end Array

def Array.const (α : Type u) {β : Type v} (default : β)
  [DecidableLessOrder α]
  [DecidableLessOrder β] : Array α β :=
⟨FiniteMap.empty α default, FiniteMap.empty.wellFormed α default⟩


end Smt
