-- Additional definitions for arrays
import data.array.lemmas

import .array.lex_order

import ..logic

import tactic.find

namespace array

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
 dsimp [push_back, read, d_array.read],
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
   simp [read, d_array.read, slice],
end

/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_list_nil {α} : to_list (@nil α) = [] := eq.refl _

end array
