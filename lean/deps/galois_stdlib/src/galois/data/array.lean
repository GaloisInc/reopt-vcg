

namespace array

/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_list_nil {α} : to_list (@nil α) = [] := eq.refl _

end array
