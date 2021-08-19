
import Std.Data.RBMap

namespace Std
namespace RBMap
universe u v w
variable {α : Type u} {β : Type v}

/- Builds an RBMap from a list with String keys. -/
def ordMap [Ord α] (entries: List (α × β))
 : RBMap α β Ord.compare :=
 RBMap.fromList entries Ord.compare


section
variable {cmp : α → α → Ordering}

@[specialize] def keys : RBMap α β cmp → List α
  | ⟨t, _⟩ => t.revFold (fun ps k _v => k::ps) []

@[specialize] def values : RBMap α β cmp → List β
  | ⟨t, _⟩ => t.revFold (fun ps _k v => v::ps) []

@[inline] def map {σ : Type w} (f : α → β → σ) : RBMap α β cmp → RBMap α σ cmp
  | ⟨t, _⟩ => t.fold (λ acc k v => acc.insert k (f k v)) RBMap.empty

/- Appends two RBMaps, with the second argument's entries overwriting
    any entries in the first argument where applicable. -/
@[specialize] def append (lhs rhs : RBMap α β cmp) : RBMap α β cmp :=
  if lhs.isEmpty then rhs
  else rhs.fold (λ m k v => m.insert k v) lhs

instance : Append (RBMap α β cmp) := ⟨RBMap.append⟩

end

end RBMap

namespace RBMap

-- It's not happy about the universes on this one if we try and add the level parameters (and even use max/ULift/etc) =\
@[inline] def mapM {α β σ : Type} {cmp : α → α → Ordering} {m : Type → Type} [Monad m] (f : α → β → m σ) : RBMap α β cmp → m (RBMap α σ cmp)
  | ⟨t, _⟩ => t.foldM (λ acc k v => acc.insert k <$> (f k v)) RBMap.empty


end RBMap
end Std
