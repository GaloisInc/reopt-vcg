namespace galois
namespace list
open list

universes u v w x
variables {α : Type u} {β : Type v}

@[simp] theorem reverse_nil : reverse (@nil α) = [] := rfl

/-- Replace reverse_core with reverse and append. -/
theorem reverse_core_simp (l r : list α) : reverse_core l r = reverse l ++ r :=
begin
  revert r,
  induction l,
  case list.nil {
    simp [reverse, reverse_core],
  },
  case list.cons : h l ind {
    intro r,
    unfold reverse,
    simp [reverse_core, ind],
  },
end

/-- Push reverse inside cons -/
@[simp] theorem reverse_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] :=
begin
  unfold reverse, unfold reverse_core,
  simp [reverse_core_simp],
end

/-- Push reverse inside append -/
@[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = reverse t ++ reverse s :=
begin
  induction s,
  case list.nil {
    simp only [nil_append, reverse_nil, append_nil],
  },
  case list.cons : h s ind {
    simp only [cons_append, reverse_cons, ind, append_assoc],
  },
end

/-- Simplify length of reverse_core -/
theorem length_reverse_core
  : Π(x y : list α), length (reverse_core x y) = length x + length y :=
begin
  intro x,
  induction x,
  case list.nil {
    intro y,
    simp only [reverse_core, length, nat.zero_add],
  },
  case list.cons : h r ind {
    intro y,
    simp only [reverse_core, ind, length, nat.add_succ, nat.add_zero, nat.succ_add],
  },
end

/-- Simplify length of reverse_core -/
theorem length_reverse (x : list α):  length (reverse x) = length x :=
by exact (length_reverse_core x nil)

@[simp] theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; [refl, simp only [*, reverse_cons, reverse_append]]; refl

/-- Convert a list into an array (whose length is the length of `l`). -/
def to_array (l : list α) : array l.length α :=
{data := λ v, l.nth_le v.1 v.2}

theorem mem_map_of_mem (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
begin
  induction l,
  case list.nil {
    cases h,
  },
  case list.cons: b l' ih  {
    cases h,
    { simp [h], },
    { exact or.inr (ih h), },
  }
end

theorem exists_of_mem_map {f : α → β} {b : β} {l : list α} (h : b ∈ map f l) : ∃ a, a ∈ l ∧ f a = b :=
begin
  induction l with c l' ih,
  case list.nil {cases h},
  case list.cons : c l' ih {
    cases (eq_or_mem_of_mem_cons h) with h h,
    case or.inl {
      exact ⟨c, mem_cons_self _ _, h.symm⟩,
    },
    case or.inr {
      cases ih h with a ha,
      exact ⟨a, mem_cons_of_mem _ ha.left, ha.right⟩
    }
  }
end

@[simp] theorem mem_map {f : α → β} {b : β} {l : list α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
⟨exists_of_mem_map, λ ⟨a, la, h⟩, by rw [← h]; exact mem_map_of_mem f la⟩

theorem nth_le_nth : ∀ {l : list α} {n} h, nth l n = some (nth_le l n h)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := @nth_le_nth l n _

@[simp] theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
| []       n     := rfl
| (a :: l) 0     := rfl
| (a :: l) (n+1) := nth_map l n

@[simp]
theorem nth_le_map (f : α → β) {l n} (H) :
  nth_le (map f l) n H = f (nth_le l n (length_map f l ▸ H)) :=
begin
  apply option.some.inj,
  rw [← nth_le_nth, nth_map, nth_le_nth]; refl,
end

end list
end galois
