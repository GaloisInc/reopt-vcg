
universe u

@[reducible]
abbrev DecidableLT (α : Type u) [LT α] :=
  ∀ (a b : α), Decidable (a < b)

class LTOrder (α : Type u) extends LT α :=
  (transitive : ∀ (x y z : α), x < y → y < z → x < z)
  (asymmetric : ∀ (x y : α), x < y → ¬(y < x))
  (total : ∀ (x y : α), x < y ∨ x = y ∨ y < x)


class DecidableLTOrder (α : Type u) extends LTOrder α :=
  (ltDec : DecidableLT α)
  (eqDec : DecidableEq α)


namespace Subtype
variable {α : Type u} {p : α → Prop}

protected
instance LT [h : LT α] : LT {x : α // p x} :=
  ⟨λ ⟨a, _⟩ ⟨b, _⟩ => a < b⟩

protected theorem lt [LT α] : ∀ {a1 a2 : {x // p x}}, a1.val < a2.val → a1 < a2
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInv [LT α] : ∀ {a1 a2 : {x // p x}}, a1 < a2 → a1.val < a2.val
  | ⟨a, h1⟩, ⟨b, h2⟩, ltPf => ltPf

protected theorem ltInvNeg [LT α] : ∀ {a1 a2 : {x // p x}}, ¬(a1.val < a2.val) → ¬(a1 < a2)
  | ⟨a, h1⟩, ⟨b, h2⟩, valNotLtPf => λ ltPf => absurd (Subtype.ltInv ltPf) valNotLtPf

protected
instance DecidableLT [LT α] [DecidableLT α] : DecidableLT {x : α // p x} :=
  fun a b =>
    if valLtPf : a.val < b.val then isTrue (Subtype.lt valLtPf)
    else isFalse (fun ltPf => absurd ltPf (Subtype.ltInvNeg valLtPf))

axiom LT.transitivity [LT α] :
  (∀ (x y z : α), x < y → y < z → x < z) →
  (∀ (x y z : {x : α // p x}), x < y → y < z → x < z)

axiom LT.asymmetry [LT α] :
  (∀ (x y : α), x < y → ¬(y < x)) →
  (∀ (x y : {x : α // p x}), x < y → ¬(y < x))

axiom LT.totality [LT α] :
  (∀ (x y : α), x < y ∨ x = y ∨ y < x) →
  (∀ (x y : {x : α // p x}), x < y ∨ x = y ∨ y < x)


instance {α : Type u} {p : α → Prop} [h : LTOrder α] : LTOrder {x : α // p x} :=
  { transitive := Subtype.LT.transitivity h.transitive,
    asymmetric := Subtype.LT.asymmetry h.asymmetric,
    total := Subtype.LT.totality h.total
  }

end Subtype


instance DecidableLTOrderImpliesDecidableLT {α : Type u} [h : DecidableLTOrder α] : DecidableLT α :=
  let h : DecidableLT α := h.ltDec;
  inferInstanceAs _

instance DecidableLTOrderImpliesDecidableEq {α : Type u} [h : DecidableLTOrder α] : DecidableEq α :=
  let h : DecidableEq α := h.eqDec;
  inferInstanceAs _



namespace DecidableLTOrder

instance {α : Type u} [h : DecidableLTOrder α] : DecidableLT α :=
  h.ltDec

instance {α : Type u} [h : DecidableLTOrder α] : DecidableEq α :=
  h.eqDec


end DecidableLTOrder
