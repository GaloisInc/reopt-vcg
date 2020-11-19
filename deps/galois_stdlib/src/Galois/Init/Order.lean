
universes u

@[reducible]
abbrev DecidableLess (α : Type u) [Less α] :=
  ∀ (a b : α), Decidable (a < b)

class LessOrder (α : Type u) extends Less α :=
  (transitive : ∀ (x y z : α), x < y → y < z → x < z)
  (asymmetric : ∀ (x y : α), x < y → ¬(y < x))
  (total : ∀ (x y : α), x < y ∨ x = y ∨ y < x)


class DecidableLessOrder (α : Type u) extends LessOrder α :=
  (ltDec : DecidableLess α)
  (eqDec : DecidableEq α)


namespace Subtype
variables {α : Type u} {p : α → Prop}

protected
instance Less [h : Less α] : Less {x : α // p x} :=
  ⟨λ ⟨a, _⟩ ⟨b, _⟩ => a < b⟩

protected theorem lt [Less α] : ∀ {a1 a2 : {x // p x}}, a1.val < a2.val → a1 < a2
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInv [Less α] : ∀ {a1 a2 : {x // p x}}, a1 < a2 → a1.val < a2.val
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInvNeg [Less α] : ∀ {a1 a2 : {x // p x}}, ¬(a1.val < a2.val) → ¬(a1 < a2)
  | ⟨a, h1⟩, ⟨b, h2⟩, valNotLtPf => λ ltPf => absurd (Subtype.ltInv ltPf) valNotLtPf

protected
instance DecidableLess [Less α] [DecidableLess α] : DecidableLess {x : α // p x} :=
  fun a b =>
    if valLtPf : a.val < b.val then isTrue (Subtype.lt valLtPf)
    else isFalse (fun ltPf => absurd ltPf (Subtype.ltInvNeg valLtPf))

axiom Less.transitivity [Less α] :
  (∀ (x y z : α), x < y → y < z → x < z) →
  (∀ (x y z : {x : α // p x}), x < y → y < z → x < z)

axiom Less.asymmetry [Less α] :
  (∀ (x y : α), x < y → ¬(y < x)) →
  (∀ (x y : {x : α // p x}), x < y → ¬(y < x))

axiom Less.totality [Less α] :
  (∀ (x y : α), x < y ∨ x = y ∨ y < x) →
  (∀ (x y : {x : α // p x}), x < y ∨ x = y ∨ y < x)


instance {α : Type u} {p : α → Prop} [h : LessOrder α] : LessOrder {x : α // p x} :=
  { transitive := Subtype.Less.transitivity h.transitive,
    asymmetric := Subtype.Less.asymmetry h.asymmetric,
    total := Subtype.Less.totality h.total
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
