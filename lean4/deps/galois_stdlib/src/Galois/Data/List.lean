
import Galois.Init.Order

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

inductive In.{u} {α : Type u} (x : α) : List α → Prop
| first : ∀ (l : List α), In (x :: l)
| rest  : ∀ (y : α) {xs : List α}, In xs → In (y :: xs)

inductive Forall.{u} {α : Type u} (p : α → Prop) : List α → Prop
| nil  : Forall []
| cons : ∀ {x : α} {xs : List α}, p x → Forall xs → Forall (x :: xs)

namespace Forall

def map.{u} {α : Type u} {p q : α → Prop} (f : ∀ {x : α}, p x → q x) : ∀ {l : List α}, Forall p l → Forall q l
| [], Forall.nil => Forall.nil
| (_::_), Forall.cons xH xsH => Forall.cons (f xH) (map xsH)

end Forall




inductive IsSortedMap.{u, v} {α : Type u} {β : Type v} [HasLessOrder α] : List (α × β) → Prop
| nil : IsSortedMap []
| cons : ∀ (k : α) (v : β) (l : List (α × β)),
         IsSortedMap l →
         l.Forall (λ (kv : (α × β)) => k < kv.fst) →
         -- N.B., HasLessOrder combined with this Forall implies
         -- no duplicate keys.
         IsSortedMap ((k,v)::l)


namespace SortedMap
universes u v
variables {α : Type u} {β : Type v}

protected def insert [DecidableLessOrder α] (k : α) (v : β) : List (α × β) →  List (α × β)
| [] => [(k,v)]
| (k0, v0)::rst =>
  if k < k0
  then (k,v)::(k0, v0)::rst
  else if k0 < k
  then (k0, v0)::(insert rst)
  else (k,v)::rst

-- FIXME prove
axiom insert.wellFormed [DecidableLessOrder α] (k : α) (v : β) {l : List (α × β)} :
List.IsSortedMap l →
List.IsSortedMap (SortedMap.insert k v l)

-- FIXME prove
axiom insert.stillNotIn [DecidableLessOrder α] (k : α) {v v' : β} (pf : v ≠ v') {l : List (α × β)} :
l.Forall (λ (kv : α × β) => kv.snd ≠ v') →
(SortedMap.insert k v l).Forall (λ (kv : α × β) => kv.snd ≠ v')


protected def erase [DecidableLessOrder α] (k : α) : List (α × β) →  List (α × β)
| [] => []
| l@((k0, v0)::rst) =>
  if k = k0
  then rst
  else if k0 > k
  then l
  else (k0,v0)::(erase rst)

-- FIXME prove
axiom erase.wellFormed [DecidableLessOrder α] (k : α) {l : List (α × β)} :
List.IsSortedMap l →
List.IsSortedMap (SortedMap.erase k l)

-- FIXME prove
axiom erase.stillNotIn [DecidableLessOrder α] (k : α) {v : β} {l : List (α × β)} :
l.Forall (λ (kv : α × β) => kv.snd ≠ v) →
(SortedMap.erase k l).Forall (λ (kv : α × β) => kv.snd ≠ v)


end SortedMap


end List
