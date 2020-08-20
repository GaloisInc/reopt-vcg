namespace List

section
universes u v
variables {α : Type u} {β : Type v}

def joinMap (f : α → List β) : List α → List β
| []      => []
| a :: as => (f a) ++ joinMap as

end

end List

namespace SortedAList
universes u v
variables {α : Type u} {β : Type v}


-- def lexLt [HasLess α] 
--           [HasLess β]
--           [forall (a1 a2 : α), Decidable (a1 < a2)]
--           [forall (b1 b2 : β), Decidable (b1 < b2)]
--           : List (α × β) → List (α × β) → Bool
-- | [], [] => false
-- | [], _::_ => true
-- | _::_, [] => false
-- | (k1, v1)::rst1, (k2, v2)::rst2 =>
--   if k1 < k2 then true
--   else if k2 < k1 then false
--   else if v1 < v2 then true
--   else if v2 < v1 then false
--   else lexLt rst1 rst2


protected def insert (lt : α → α → Bool) (k : α) (v : β) : List (α × β) →  List (α × β)
| [] => [(k,v)]
| (k0, v0)::rst =>
  if lt k k0
  then (k,v)::(k0, v0)::rst
  else if lt k0 k
  then (k0, v0)::(insert rst)
  else (k,v)::rst

end SortedAList

