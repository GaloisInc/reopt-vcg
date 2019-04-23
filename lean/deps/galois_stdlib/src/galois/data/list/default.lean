import .nth_le
import .with_mem

namespace list

/-- Take conjunction of all propositions in list. -/
protected
def forall_prop : list Prop → Prop
| [] := true
| (h::r) := h ∧ forall_prop r

section is_empty

/-- Return true if list is empty -/
def is_empty {α: Type _} : list α → Prop
| [] := true
| (_::_) := false

/-- Decide whether list is empty -/
instance is_empty.decidable (α: Type _) : decidable_pred (@is_empty α)
| [] := decidable.is_true trivial
| (_::_) := decidable.is_false id

end is_empty

theorem map_eq_nil {α} {β} (f : α → β)  (l:list α) : (list.map f l = nil) ↔ (l = nil) :=
begin
  cases l; simp [map],
end

end list
