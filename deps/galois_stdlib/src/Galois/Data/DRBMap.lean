
import Std.Data.RBMap

namespace Sigma
universes u v
variables {α : Type u} {β : α → Type v}

instance [Inhabited α] [forall (a : α), Inhabited (β a)] : Inhabited (Sigma β) :=
{default := let a : α := arbitrary; ⟨a, (arbitrary : (β a)) ⟩}

end Sigma



namespace Std
universes u v w w'

namespace RBNode
variables {α : Type u} {β : α → Type v} (lt : α → α → Bool)

@[specialize] def findEq [DecidableEq α] : RBNode α β → ∀ (k : α), Option (β k)
| RBNode.leaf,             x => none
| RBNode.node _ a ky vy b, x =>
  if hEq : ky = x
  then some $ cast (congrArg β hEq) vy
  else if lt x ky then findEq a x
  else findEq b x

end RBNode

open Std.RBNode

def DRBMap (α : Type u) (β : α → Type v) (lt : α → α → Bool) : Type (max u v) :=
{t : RBNode α β // t.WellFormed lt }


@[inline] def mkDRBMap (α : Type u) (β : α → Type v) (lt : α → α → Bool) : DRBMap α β lt :=
⟨leaf, WellFormed.leafWff⟩

@[inline] def DRBMap.empty {α : Type u} {β : α → Type v} {lt : α → α → Bool} : DRBMap α β lt :=
mkDRBMap _ _ _

-- instance DRBMap.HasEmptyc (α : Type u) (β : α → Type v) (lt : α → α → Bool) : HasEmptyc (DRBMap α β lt) :=
-- ⟨DRBMap.empty⟩

namespace DRBMap
variables {α : Type u} {β : α → Type v} {σ : Type w} {lt : α → α → Bool}


def depth (f : Nat → Nat → Nat) (t : DRBMap α β lt) : Nat :=
t.val.depth f

@[inline] def fold (f : σ → forall (a : α), (β a) → σ) : σ → DRBMap α β lt → σ
| b, ⟨t, _⟩ => t.fold f b

@[inline] def revFold (f : σ → forall (a : α), (β a) → σ) : σ → DRBMap α β lt → σ
| b, ⟨t, _⟩ => t.revFold f b

@[inline] def foldM {m : Type w → Type w'} [Monad m] (f : σ → forall (a : α), (β a) → m σ) : σ → DRBMap α β lt → m σ
| b, ⟨t, _⟩ => t.foldM f b

@[inline] def forM {m : Type w → Type w'} [Monad m] (f : forall (a : α), (β a) → m PUnit) (t : DRBMap α β lt) : m PUnit :=
t.foldM (fun _ k v => f k v) ⟨⟩

@[inline] def isEmpty : DRBMap α β lt → Bool
| ⟨leaf, _⟩ => true
| _         => false

@[specialize] def toList : DRBMap α β lt → List (Sigma β)
| ⟨t, _⟩ => t.revFold (fun ps k v => ⟨k, v⟩::ps) []

@[inline] protected def min : DRBMap α β lt → Option (Sigma β)
| ⟨t, _⟩ =>
  match t.min with
  | some ⟨k, v⟩ => some ⟨k, v⟩
  | none        => none

@[inline] protected def max : DRBMap α β lt → Option (Sigma β)
| ⟨t, _⟩ =>
  match t.max with
  | some ⟨k, v⟩ => some ⟨k, v⟩
  | none        => none

instance [Repr α] [forall (a : α), Repr (β a)] : Repr (DRBMap α β lt) :=
⟨fun t => "rbmapOf " ++ repr t.toList⟩

@[inline] def insert : DRBMap α β lt → forall (a : α), (β a) → DRBMap α β lt
| ⟨t, w⟩, k, v => ⟨t.insert lt k v, WellFormed.insertWff w rfl⟩

@[inline] def erase : DRBMap α β lt → α → DRBMap α β lt
| ⟨t, w⟩, k => ⟨t.erase lt k, WellFormed.eraseWff w rfl⟩

@[specialize] def ofList : List (Sigma β) → DRBMap α β lt
| []        => mkDRBMap _ _ _
| ⟨k,v⟩::xs => (ofList xs).insert k v

@[inline] def find? : DRBMap α β lt → α → Option (Sigma β)
| ⟨t, _⟩, x => t.findCore lt x

@[inline] def findEq? [DecidableEq α] : DRBMap α β lt → forall (a : α), Option (β a)
| ⟨t, _⟩, x => t.findEq lt x

@[inline] def findD (t : DRBMap α β lt) (k : α) (v₀ : Sigma β) : Sigma β :=
(t.find? k).getD v₀

@[inline] def findEqD [DecidableEq α] (t : DRBMap α β lt) (k : α) (v₀ : β k) : β k :=
(t.findEq? k).getD v₀


/-- (lowerBound k) retrieves the kv pair of the largest key smaller than or equal to `k`,
    if it exists. -/
@[inline] def lowerBound : DRBMap α β lt → α → Option (Sigma β)
| ⟨t, _⟩, x => t.lowerBound lt x none

@[inline] def contains (t : DRBMap α β lt) (a : α) : Bool :=
(t.find? a).isSome

@[inline] def fromList (l : List (Sigma β)) (lt : α → α → Bool) : DRBMap α β lt :=
l.foldl (fun r p => r.insert p.1 p.2) (mkDRBMap α β lt)

@[inline] def all : DRBMap α β lt → (forall (a : α), β a → Bool) → Bool
| ⟨t, _⟩, p => t.all p

@[inline] def any : DRBMap α β lt → (forall (a : α), β a → Bool) → Bool
| ⟨t, _⟩, p => t.any p

def size (m : DRBMap α β lt) : Nat :=
m.fold (fun sz _ _ => sz+1) 0

def maxDepth (t : DRBMap α β lt) : Nat :=
t.val.depth Nat.max


@[inline] def min! [Inhabited α] [forall (a : α), Inhabited (β a)] (t : DRBMap α β lt) : Sigma β :=
match t.min with
| some p => p
| none   => panic! "map is empty"

@[inline] def max! [Inhabited α] [forall (a : α), Inhabited (β a)] (t : DRBMap α β lt) : Sigma β :=
match t.max with
| some p => p
| none   => panic! "map is empty"

@[inline] def find! [Inhabited α] [forall (a : α), Inhabited (β a)] (t : DRBMap α β lt) (k : α) : Sigma β :=
match t.find? k with
| some b => b
| none   => panic! "key is not in the map"

@[inline] def findEq! [DecidableEq α] [Inhabited α] [forall (a : α), Inhabited (β a)] (t : DRBMap α β lt) (k : α) : β k :=
match t.findEq? k with
| some b => b
| none   => panic! "key is not in the map"


end DRBMap

def drbmapOf {α : Type u} {β : α → Type v} (l : List (Sigma β)) (lt : α → α → Bool) : DRBMap α β lt :=
DRBMap.fromList l lt

end Std
