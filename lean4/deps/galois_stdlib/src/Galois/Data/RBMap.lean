
namespace RBMap
universes u v w
variables {α : Type u} {β : Type v}

/-- Builds an RBMap from a list with String keys. --/
def ltMap [HasLess α] [∀ (a b : α), Decidable (a < b)] (entries: List (α × β))
 : RBMap α β (λ (x y:α)=> x<y) :=
RBMap.fromList entries (λ (x y:α)=> x<y)


section
variable {lt : α → α → Bool}

@[specialize] def keys : RBMap α β lt → List α
| ⟨t, _⟩ => t.revFold (fun ps k _v => k::ps) []

@[specialize] def values : RBMap α β lt → List β
| ⟨t, _⟩ => t.revFold (fun ps _k v => v::ps) []
end

end RBMap
