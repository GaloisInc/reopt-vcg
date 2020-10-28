
import Std.Data.RBMap

namespace Std
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

@[inline] def map {σ : Type w} (f : α → β → σ) : RBMap α β lt → RBMap α σ lt
| ⟨t, _⟩ => t.fold (λ acc k v => acc.insert k (f k v)) RBMap.empty

/-- Appends two RBMaps, with the second argument's entries overwriting
    any entries in the first argument where applicable. --/
@[specialize] def append (lhs rhs : RBMap α β lt) : RBMap α β lt :=
if lhs.isEmpty then rhs
else rhs.fold (λ m k v => m.insert k v) lhs

instance : HasAppend (RBMap α β lt) := ⟨RBMap.append⟩

end

end RBMap

namespace RBMap

-- It's not happy about the universes on this one if we try and add the level parameters (and even use max/ULift/etc) =\
@[inline] def mapM {α β σ : Type} {lt : α → α → Bool} {m : Type → Type} [Monad m] (f : α → β → m σ) : RBMap α β lt → m (RBMap α σ lt)
| ⟨t, _⟩ => t.foldM (λ acc k v => acc.insert k <$> (f k v)) RBMap.empty


end RBMap
end Std
