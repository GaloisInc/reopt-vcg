namespace List

def qsort.{u} {α : Type} [Inhabited α] (as : List α) (lt : α → α → Bool) : List α :=
let arr := as.toArray;
(arr.qsort lt 0 (arr.size - 1)).toList


def joinMap.{u,v} {α : Type u} {β : Type v} (f : α → List β) : List α → List β
| []      => []
| a :: as => (f a) ++ joinMap as


-- Powerset of a single list.
def powerset.{u} {α : Type u} : List α → List (List α)
| [] => [[]]
| x::xs =>
  joinMap (λ l => [l, x::l]) (powerset xs)

-- Cartesian product of two lists.
def product.{u, v} {α : Type u} {β : Type v} : List α → List β → List (α × β)
| [], _ => []
| a::as, bs => (bs.map (λ b => (a,b)))++(product as bs)

-- List.power xs ys computes ys^xs, or the set of sequences of elements of ys indexed by elements of xs.
def power {α β} : List α → List β → List (List (α × β))
| [] , vs => []
| k::ks, vs => (power ks vs).joinMap (λ m => vs.map (λ v => (k, v)::m))

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


protected def insert [HasLess α] [forall (x y:α), Decidable (x < y)] (k : α) (v : β) : List (α × β) →  List (α × β)
| [] => [(k,v)]
| (k0, v0)::rst =>
  if k < k0
  then (k,v)::(k0, v0)::rst
  else if k0 < k
  then (k0, v0)::(insert rst)
  else (k,v)::rst

end SortedAList

