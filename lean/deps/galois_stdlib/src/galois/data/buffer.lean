/-
Provides a decidable_eq instance for buffer.
-/
import data.buffer.basic -- from mathlib

import galois.data.array

namespace buffer

theorem to_list_length {α} (b: buffer α)
: list.length (buffer.to_list b) = b.size :=
begin
  simp only [buffer.to_list, size, array.to_list_length],
end

/-- Replace nil.to_list with empty list. -/
@[simp]
theorem nil_to_list (α:Type _) : (@buffer.nil α).to_list = [] := refl []

/-- Convert read to list read so we can use list lemmas -/
theorem read_to_nth_le {α} (b: buffer α) (i:fin b.size)
: buffer.read b i = list.nth_le b.to_list i.val ((to_list_length b).symm ▸ i.is_lt) :=
begin
  cases b with n a,
  simp only [read, to_list, array.to_list_nth_le', to_array],
end


/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_array_mk_buffer {α} : to_array mk_buffer = @array.nil α :=
begin
  apply array.ext,
  intro i,
  have h : false := fin.elim0 i,
  contradiction,
end

/-- Converting list to bufer and back is round trip. -/
theorem to_list_to_buffer {α} (l:list α) : l.to_buffer.to_list = l :=
begin
  unfold list.to_buffer,
  simp only [to_list_append_list],
  simp only [to_list, to_array_mk_buffer, array.to_list_nil, list.nil_append],
end

/- Simplify functions calling through as_string -/
theorem to_char_buffer_as_string (l:list char)
: l.as_string.to_char_buffer = l.to_buffer := eq.refl l.to_buffer

end buffer
