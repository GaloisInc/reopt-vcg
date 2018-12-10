namespace list

/-- Take conjunction of all propositions in list. -/
protected
def forall_prop : list Prop → Prop
| [] := true
| (h::r) := h ∧ forall_prop r

end list
