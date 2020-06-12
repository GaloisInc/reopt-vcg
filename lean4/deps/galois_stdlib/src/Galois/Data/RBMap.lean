
namespace RBMap
universes u v w
variables {α : Type u} {β : Type v} {σ : Type w} {lt : α → α → Bool}

@[specialize] def keys : RBMap α β lt → List α
| ⟨t, _⟩ => t.revFold (fun ps k _v => k::ps) []

@[specialize] def values : RBMap α β lt → List β
| ⟨t, _⟩ => t.revFold (fun ps _k v => v::ps) []


end RBMap
