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


/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_list_nil {α} : to_list (@nil α) = [] := eq.refl _

end array
