/-
This defines functionality that could be in data.rbmap
-/
import galois.data.rbtree

namespace rbmap
universes u v

variables {α : Type u} {β : Type v} {lt : α → α → Prop}

/- Expose the rbmap_lt as a decidable instance -/
local attribute [instance] rbmap_lt_dec

instance  [h : decidable_rel lt] (k : α) (m:rbmap α β lt) : decidable (k ∈ m) :=
begin
  cases m with tree prop,
  cases tree;
  {
    simp [has_mem.mem, rbmap.mem, rbtree.mem],
    apply_instance,
  },
end

end rbmap
