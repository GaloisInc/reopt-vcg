-- Definitions

--- Use type-class resolution to find a decidable instance.
def decide (p:Prop) [h:decidable p] : decidable p := h


--- Use decidable instance to prove any theorem is we have a proof of the theorem, but it is false.
theorem  of_as_false {P : Prop} [h:decidable P] (p:P) (q : as_false P) {α : Prop} : α :=
begin
  simp [as_false] at q, contradiction,
end

inductive PropExists {α : Prop} (p : α → Prop) : Prop
| intro (w : α) (h : p w) : PropExists
