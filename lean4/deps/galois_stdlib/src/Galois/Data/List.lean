namespace List

section
universes u v
variables {α : Type u} {β : Type v}

def joinMap (f : α → List β) : List α → List β
| []      => []
| a :: as => (f a) ++ joinMap as

end

def lexLt {α} (lt : α → α → Bool) : List α → List α → Bool
| [], [] => false
| [], y::ys => true
| x::xs, [] => false
| x::xs, y::ys =>
  if lt x y then true
  else if lt y x then false
  else lexLt xs ys

end List

namespace SortedAList
universes u v
variables {α : Type u} {β : Type v} (lt : α → α → Bool)


protected def insert (k : α) (v : β) : List (α × β) →  List (α × β)
| [] => [(k,v)]
| (k0, v0)::rst =>
  if lt k k0
  then (k,v)::(k0, v0)::rst
  else if lt k0 k
  then (k0, v0)::(insert rst)
  else (k,v)::rst

end SortedAList

