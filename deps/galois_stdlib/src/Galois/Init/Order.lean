
universes u

@[reducible]
abbrev DecidableLess (α : Type u) [HasLess α] :=
  ∀ (a b : α), Decidable (a < b)

class LessOrder (α : Type u) extends HasLess α :=
  (transitive : ∀ (x y z : α), x < y → y < z → x < z)
  (asymmetric : ∀ (x y : α), x < y → ¬(y < x))
  (total : ∀ (x y : α), x < y ∨ x = y ∨ y < x)


class DecidableLessOrder (α : Type u) extends LessOrder α :=
  (ltDec : DecidableLess α)
  (eqDec : DecidableEq α)


namespace Subtype
variables {α : Type u} {p : α → Prop}

protected
instance HasLess [h : HasLess α] : HasLess {x : α // p x} :=
  ⟨λ ⟨a, _⟩ ⟨b, _⟩ => a < b⟩

protected theorem lt [HasLess α] : ∀ {a1 a2 : {x // p x}}, a1.val < a2.val → a1 < a2
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInv [HasLess α] : ∀ {a1 a2 : {x // p x}}, a1 < a2 → a1.val < a2.val
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInvNeg [HasLess α] : ∀ {a1 a2 : {x // p x}}, ¬(a1.val < a2.val) → ¬(a1 < a2)
  | ⟨a, h1⟩, ⟨b, h2⟩, valNotLtPf => λ ltPf => absurd (Subtype.ltInv ltPf) valNotLtPf

protected
instance DecidableLess [HasLess α] [DecidableLess α] : DecidableLess {x : α // p x} :=
  fun a b =>
    if valLtPf : a.val < b.val then isTrue (Subtype.lt valLtPf)
    else isFalse (fun ltPf => absurd ltPf (Subtype.ltInvNeg valLtPf))

axiom HasLess.transitivity [HasLess α] :
  (∀ (x y z : α), x < y → y < z → x < z) →
  (∀ (x y z : {x : α // p x}), x < y → y < z → x < z)

axiom HasLess.asymmetry [HasLess α] :
  (∀ (x y : α), x < y → ¬(y < x)) →
  (∀ (x y : {x : α // p x}), x < y → ¬(y < x))

axiom HasLess.totality [HasLess α] :
  (∀ (x y : α), x < y ∨ x = y ∨ y < x) →
  (∀ (x y : {x : α // p x}), x < y ∨ x = y ∨ y < x)


instance {α : Type u} {p : α → Prop} [h : LessOrder α] : LessOrder {x : α // p x} :=
  { transitive := Subtype.HasLess.transitivity h.transitive,
    asymmetric := Subtype.HasLess.asymmetry h.asymmetric,
    total := Subtype.HasLess.totality h.total
  }

end Subtype


instance DecidableLessOrderImpliesDecidableLess {α : Type u} [h : DecidableLessOrder α] : DecidableLess α :=
  let h : DecidableLess α := h.ltDec;
  inferInstanceAs _

instance DecidableLessOrderImpliesDecidableEq {α : Type u} [h : DecidableLessOrder α] : DecidableEq α :=
  let h : DecidableEq α := h.eqDec;
  inferInstanceAs _



namespace DecidableLessOrder

instance {α : Type u} [h : DecidableLessOrder α] : DecidableLess α :=
  h.ltDec

instance {α : Type u} [h : DecidableLessOrder α] : DecidableEq α :=
  h.eqDec


end DecidableLessOrder
