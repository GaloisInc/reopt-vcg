
variable {α:Type _}

namespace galois

lemma le_of_not_lt [linear_order α] {a b : α} : ¬ a < b → b ≤ a := le_of_not_gt

lemma not_lt_of_le [preorder α] {a b : α} (h : a ≤ b) : ¬ b < a
| hab := not_le_of_gt hab h

-- Simplify not-less than (mathlib alt)
@[simp]
lemma not_lt [linear_order α] {a b : α} : ¬ a < b ↔ b ≤ a := ⟨le_of_not_gt, not_lt_of_ge⟩

-- Simplify not-less than or equal (mathlib alt)
@[simp]
lemma not_le [linear_order α] {a b : α} : ¬ a ≤ b ↔ b < a := ⟨lt_of_not_ge, not_le_of_gt⟩

lemma lt_imp_lt_of_le_imp_le {β} [linear_order α] [preorder β] {a b : α} {c d : β}
  (H : a ≤ b → c ≤ d) (h : d < c) : b < a :=
lt_of_not_ge $ λ h', not_lt_of_ge (H h') h

lemma le_imp_le_of_lt_imp_lt {β} [preorder α] [linear_order β] {a b : α} {c d : β}
  (H : d < c → b < a) (h : a ≤ b) : c ≤ d :=
le_of_not_gt $ λ h', not_le_of_gt (H h') h

end galois
