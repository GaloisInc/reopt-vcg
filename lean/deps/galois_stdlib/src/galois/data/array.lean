-- Additional definitions for arrays

import .array.lex_order

import ..algebra.order
import ..data.nat.basic
import ..data.list
import ..logic

namespace galois
open array

namespace array
universe u

/- rev_list -/

section rev_list
variables {n : ℕ} {α : Type u} {a : array n α}

theorem rev_list_reverse_aux : ∀ i (h : i ≤ n) (t : list α),
  (a.iterate_aux (λ _, (::)) i h []).reverse_core t = a.rev_iterate_aux (λ _, (::)) i h t
| 0     h t := rfl
| (i+1) h t := rev_list_reverse_aux i _ _

@[simp] theorem rev_list_reverse : a.rev_list.reverse = a.to_list :=
rev_list_reverse_aux _ _ _

@[simp] theorem to_list_reverse : a.to_list.reverse = a.rev_list :=
by rw [←rev_list_reverse, list.reverse_reverse]

end rev_list

/- length -/

section length
variables {n : ℕ} {α : Type u}

theorem rev_list_length_aux (a : array n α) (i h) :
  (a.iterate_aux (λ _, (::)) i h []).length = i :=
by induction i; simp [*, d_array.iterate_aux]

@[simp] theorem rev_list_length (a : array n α) : a.rev_list.length = n :=
rev_list_length_aux a _ _

@[simp] theorem to_list_length (a : array n α) : a.to_list.length = n :=
by rw[←rev_list_reverse, list.length_reverse, rev_list_length]

end length

/- nth -/

section nth
variables {n : ℕ} {α : Type u} {a : array n α}

theorem to_list_nth_le_aux (i : ℕ) (ih : i < n) : ∀ j {jh t h'},
  (∀ k tl, j + k = i → list.nth_le t k tl = a.read ⟨i, ih⟩) →
  (a.rev_iterate_aux (λ _, (::)) j jh t).nth_le i h' = a.read ⟨i, ih⟩
| 0     _  _ _  al := al i _ $ zero_add _
| (j+1) jh t h' al := to_list_nth_le_aux j $ λ k tl hjk,
  show list.nth_le (a.read ⟨j, jh⟩ :: t) k tl = a.read ⟨i, ih⟩, from
  match k, hjk, tl with
  | 0,    e, tl := match i, e, ih with ._, rfl, _ := rfl end
  | k'+1, _, tl := by simp[list.nth_le]; exact al _ _ (by simp [*])
  end

theorem to_list_nth_le (i : ℕ) (h h') : list.nth_le a.to_list i h' = a.read ⟨i, h⟩ :=
to_list_nth_le_aux _ _ _ (λ k tl, absurd tl k.not_lt_zero)

@[simp] theorem to_list_nth_le' (a : array n α) (i : fin n) (h') :
  list.nth_le a.to_list i.1 h' = a.read i :=
by cases i; apply to_list_nth_le

end nth

/- to_array -/

section to_array
variables {n : ℕ} {α : Type u}

@[simp] theorem to_list_to_array (a : array n α) : list.to_array a.to_list == a :=
heq_of_heq_of_eq
  (@@eq.drec_on (λ m (e : a.to_list.length = m), (d_array.mk (λ v, a.to_list.nth_le v.1 v.2)) ==
    (@d_array.mk m (λ _, α) $ λ v, a.to_list.nth_le v.1 $ e.symm ▸ v.2)) (array.to_list_length a) heq.rfl) $
  d_array.ext $ λ ⟨i, h⟩, to_list_nth_le i h _

end to_array

section push_back
variables {n : ℕ} {α : Type u} {v : α} {a : array n α}

lemma push_back_rev_list_aux : ∀ i h h',
  d_array.iterate_aux (a.push_back v) (λ _, (::)) i h [] = d_array.iterate_aux a (λ _, (::)) i h' []
| 0 h h' := rfl
| (i+1) h h' := begin
  simp [d_array.iterate_aux],
  refine ⟨_, push_back_rev_list_aux _ _ _⟩,
  dsimp [array.read, d_array.read, array.push_back],
  rw [dif_neg], refl,
  exact ne_of_lt h',
end

@[simp] theorem push_back_rev_list : (a.push_back v).rev_list = v :: a.rev_list :=
begin
  unfold array.push_back array.rev_list array.foldl array.iterate d_array.iterate,
  dsimp [d_array.iterate_aux, array.read, d_array.read, array.push_back],
  rw [dif_pos (eq.refl n)],
  apply congr_arg,
  apply push_back_rev_list_aux
end

@[simp] theorem push_back_to_list : (a.push_back v).to_list = a.to_list ++ [v] :=
by rw [←rev_list_reverse, ←rev_list_reverse, push_back_rev_list, list.reverse_cons]

end push_back

/- Simplification rule for reading from an array constructed by push_back with a less-than test. -/
theorem read_push_back_lt_iff {α} {n:ℕ} (a : array n α) (x:α) (i : fin (n+1))
: read (push_back a x) i =
  if lt:i.val < n then
    read a ⟨i.val,lt⟩
  else
    x :=
begin
 cases i with i i_lt_plus_1,
 have i_le := nat.le_of_succ_le_succ i_lt_plus_1,
 dsimp [push_back, array.read, d_array.read],
 cases (decide (i = n)),
 case decidable.is_true  : is_eq {
   simp [is_eq],
 },
 case decidable.is_false : is_neq {
   have i_lt := lt_of_le_of_ne i_le is_neq,
   simp [is_neq, i_lt],
 },
end

/-- Lemma needed for stating read_slice below -/
theorem read_slice.len (s:ℕ) {e n:ℕ} (e_le_n : e ≤ n) (i:fin (e - s))
: s + i.val < n :=
    calc s + i.val = i.val + s : add_comm _ _
               ... < e : nat.add_lt_of_lt_sub_right i.is_lt
               ... ≤ n : e_le_n

/- Simplify read (slice ...) -/
theorem read_slice {n:ℕ} {α} (a:array n α) (s e :ℕ) (s_le_e : s ≤ e) (e_le_n : e ≤ n) (i:fin (e - s))
: read (slice a s e s_le_e e_le_n) i = read a ⟨s + i.val, read_slice.len s e_le_n i⟩ :=
begin
   cases a with f,
   cases i,
   simp [array.read, d_array.read, slice],

end

/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_list_nil {α} : to_list (@nil α) = [] := eq.refl _

end array

end galois
