/-
Data definitions used for the denotation of SMT arrays.

Copyright (c) 2020 Galois Inc. All rights reserved.
-/

import Galois.Data.List
import Galois.Init.Order

namespace Smt
universe u v

/- A finite representation of a map/array, with a set of entries
    stored in a association list and a default value to return
    when a key is not found.  -/
structure FiniteMap (α : Type u) (β : Type v) : Type (max u v) :=
  (entries : List (α × β))
  (default : β)

namespace FiniteMap

@[reducible]
def empty (α : Type u) {β : Type v} (default : β) : FiniteMap α β :=
  ⟨[], default⟩

section
variable {α : Type u} {β : Type v}

protected
def FiniteMap.decEq
  [DecidableEq α]
  [DecidableEq β]
  : ∀ (fm1 fm2 : FiniteMap α β), Decidable (fm1 = fm2)
  | ⟨es1, d1⟩, ⟨es2, d2⟩ =>
    match decEq es1 es2, decEq d1 d2 with
    | isTrue e₁, isTrue e₂ => isTrue (e₁ ▸ e₂ ▸ rfl)
    | isFalse n₁, _ => isFalse (fun h => FiniteMap.noConfusion h $ fun e₁ _ => absurd e₁ n₁)
    | isTrue _, isFalse n₂ => isFalse (fun h => FiniteMap.noConfusion h $ fun _ e₂ => absurd e₂ n₂)


instance [DecidableEq α] [DecidableEq β] : DecidableEq (FiniteMap α β) :=
  FiniteMap.decEq

def FiniteMap.less [LT α] [LT β] : FiniteMap α β → FiniteMap α β → Prop
  | a1, a2 => (a1.entries, a1.default) < (a2.entries, a2.default)

protected
instance FiniteMap.LT [LT α] [LT β] : LT (FiniteMap α β) :=
  ⟨@FiniteMap.less α β _ _⟩


def FiniteMap.decLt
  [DecidableEq α]
  [DecidableEq β]
  [LT α]
  [LT β]
  [DecidableLT α]
  [DecidableLT β]
  : ∀ (fm1 fm2 : FiniteMap α β),
    Decidable (fm1 < fm2)
  | ⟨es1, d1⟩, ⟨es2, d2⟩ =>
    let prodLtDec : ∀ (p1 p2 : (α × β)), Decidable (p1 < p2) := prodHasDecidableLt
    let listLtDec : ∀ (l1 l2 : List (α × β)), Decidable (l1 < l2) := List.hasDecidableLt
    inferInstanceAs (Decidable ((es1, d1) < (es2, d2)))


instance FiniteMap.DecidableLT
  [DecidableEq α]
  [DecidableEq β]
  [LT α]
  [LT β]
  [DecidableLT α]
  [DecidableLT β]
  : ∀ (x y : FiniteMap α β), Decidable (x < y) :=
  FiniteMap.decLt


end

-- FIXME prove when tactics are enabled
theorem LT.transitivity {α : Type u} {β : Type v}
 [LT α] [LT β]
 [DecidableEq α] [DecidableEq β] :
 (∀ (x y z : α), x < y → y < z → x < z) →
 (∀ (x y z : β), x < y → y < z → x < z) →
 (∀ (x y z : FiniteMap α β), x < y → y < z → x < z) :=
 sorry

-- FIXME prove when tactics are enabled
theorem LT.asymmetry {α : Type u} {β : Type v}
 [LT α] [LT β]
 [DecidableEq α] [DecidableEq β] :
 (∀ (x y : α), x < y → ¬(y < x)) →
 (∀ (x y : β), x < y → ¬(y < x)) →
 (∀ (x y : FiniteMap α β), x < y → ¬(y < x)) :=
 sorry

-- FIXME prove when tactics are enabled
theorem LT.totality {α : Type u} {β : Type v}
 [LT α] [LT β]
 [DecidableEq α] [DecidableEq β] :
 (∀ (x y : α), x < y ∨ x = y ∨ y < x) →
 (∀ (x y : β), x < y ∨ x = y ∨ y < x) →
 (∀ (x y : FiniteMap α β), x < y ∨ x = y ∨ y < x) :=
 sorry

instance {α : Type u} {β : Type v}
  [DecidableEq α] [DecidableEq β]
  [LT α] [LT β]
  [hA : LTOrder α] [hB : LTOrder β]
  : LTOrder (FiniteMap α β) :=
  -- FIXME why don't these definitions work...?
  { transitive := sorry, --FiniteMap.LT.transitivity hA.transitive hB.transitive,
    asymmetric := sorry, --FiniteMap.LT.asymmetry hA.asymmetric hB.asymmetric,
    total := sorry --FiniteMap.LT.totality hA.total hB.total
  }

/-- A well-formed FiniteMap has sorted entries and no default values
   stored in it's association list, which means Lean definitional equality
   corresponds to extensional equality for arrays. -/
structure WellFormed {α : Type u} {β : Type v} (fm : FiniteMap α β)
  [DecidableLTOrder α]
  [DecidableLTOrder β] : Prop :=
  (sorted : fm.entries.SortedMap)
  (noDefault : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default))

def empty.wellFormed (α : Type u) {β : Type v}
  [DecidableLTOrder α]
  [DecidableLTOrder β]
  (v : β) : FiniteMap.WellFormed (FiniteMap.empty α v) :=
  let hSM : List.SortedMap (FiniteMap.empty α v).entries := @List.SortedMap.nil α β _;
  ⟨hSM, List.Forall.nil⟩

end FiniteMap


/-- An Array is simply a FiniteMap with a unique representation (imposed by
    the well-formedness requirement). -/
def Array (α : Type u) (β : Type v)
  [DecidableLTOrder α]
  [DecidableLTOrder β] : Type (max u v) :=
{fm : FiniteMap α β // FiniteMap.WellFormed fm}

-- #check Subtype.Inhabited

namespace Array
variable {α : Type u} {β : Type v}

open Subtype

instance [hA : DecidableLTOrder α] [hB : DecidableLTOrder β] : DecidableEq (Array α β) :=
  inferInstanceAs (DecidableEq {fm : FiniteMap α β // FiniteMap.WellFormed fm})

instance [hA : DecidableLTOrder α] [hB : DecidableLTOrder β] : LT (Array α β) :=
  inferInstanceAs (LT {fm : FiniteMap α β // FiniteMap.WellFormed fm})

instance [hA : DecidableLTOrder α] [hB : DecidableLTOrder β] : DecidableLT (Array α β) :=
  inferInstanceAs (DecidableLT {fm : FiniteMap α β // FiniteMap.WellFormed fm})

instance [hA : DecidableLTOrder α] [hB : DecidableLTOrder β] : LTOrder (Array α β) :=
  inferInstanceAs (LTOrder {fm : FiniteMap α β // FiniteMap.WellFormed fm})

instance [hA : DecidableLTOrder α] [hB : DecidableLTOrder β] : DecidableLTOrder (Array α β) :=
  { eqDec := inferInstanceAs (DecidableEq (Array α β)),
    ltDec := inferInstanceAs (DecidableLT (Array α β))
  }


section Operations
variable [DecidableLTOrder α] [DecidableLTOrder β]

def select (a : Array α β) (k : α) : β :=
match a.val.entries.lookup k with
| some v => v
| none => a.val.default


def store (a : Array α β) (k : α) (v : β) : Array α β :=
if h : v = a.val.default
then
  let fm : FiniteMap α β := {a.val with entries := List.SortedMap.erase k a.val.entries};
  have h1 : fm.entries.SortedMap :=
    List.SortedMap.erase.wellFormed k a.property.sorted;
  have h2 : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default) :=
    List.SortedMap.erase.stillNotIn k a.property.noDefault;
  ⟨fm, ⟨h1, h2⟩⟩
else
  let fm : FiniteMap α β := {a.val with entries := List.SortedMap.insert k v a.val.entries};
  have h1 : fm.entries.SortedMap := List.SortedMap.insert.wellFormed k v a.property.sorted;
  have h2 : fm.entries.Forall (λ (kv : α × β) => kv.snd ≠ fm.default) :=
    List.SortedMap.insert.stillNotIn k h a.property.noDefault;
  ⟨fm, ⟨h1, h2⟩⟩

end Operations

end Array

def Array.const (α : Type u) {β : Type v} (default : β)
  [DecidableLTOrder α]
  [DecidableLTOrder β] : Array α β :=
⟨FiniteMap.empty α default, FiniteMap.empty.wellFormed α default⟩


end Smt
