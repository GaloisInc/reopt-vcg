
import Galois.Init.Order

namespace List

universes u v

def qsort {α : Type} [Inhabited α] (as : List α) (lt : α → α → Bool) : List α :=
  let arr := as.toArray;
  (arr.qsort lt 0 (arr.size - 1)).toList


def joinMap {α : Type u} {β : Type v} (f : α → List β) : List α → List β
  | []      => []
  | a :: as => (f a) ++ joinMap f as


-- Powerset of a single list.
def powerset {α : Type u} : List α → List (List α)
| [] => [[]]
| x::xs =>
  joinMap (λ l => [l, x::l]) (powerset xs)

-- Cartesian product of two lists.
def product {α : Type u} {β : Type v} : List α → List β → List (α × β)
| [], _ => []
| a::as, bs => (bs.map (λ b => (a,b)))++(product as bs)

-- List.power xs ys computes ys^xs, or the set of sequences of elements of ys indexed by elements of xs.
def power {α β} : List α → List β → List (List (α × β))
| [] , vs => []
| k::ks, vs => (power ks vs).joinMap (λ m => vs.map (λ v => (k, v)::m))

inductive In {α : Type u} (x : α) : List α → Prop
| first : ∀ (l : List α), In x (x :: l)
| rest  : ∀ (y : α) {xs : List α}, In x xs → In x (y :: xs)

inductive Forall {α : Type u} (p : α → Prop) : List α → Prop
| nil  : Forall p []
| cons : ∀ {x : α} {xs : List α}, p x → Forall p xs → Forall p (x :: xs)

namespace Forall

def map {α : Type u} {p q : α → Prop} (f : ∀ {x : α}, p x → q x) : ∀ {l : List α}, Forall p l → Forall q l
| [], Forall.nil => Forall.nil
| (_::_), Forall.cons xH xsH => Forall.cons (f xH) (map f xsH)

end Forall




inductive SortedMap {α : Type u} {β : Type v} [LessOrder α] : List (α × β) → Prop
  | nil : SortedMap []
  | cons : ∀ (k : α) (v : β) (l : List (α × β)),
           SortedMap l →
           l.Forall (λ (kv : (α × β)) => k < kv.fst) →
           -- N.B., HasLessOrder combined with this Forall implies
           -- no duplicate keys.
           SortedMap ((k,v)::l)


namespace SortedMap
variables {α : Type u} {β : Type v}

protected def insert [DecidableLessOrder α] (k : α) (v : β) : List (α × β) →  List (α × β)
| [] => [(k,v)]
| (k0, v0)::rst =>
  if k < k0
  then (k,v)::(k0, v0)::rst
  else if k0 < k
  then (k0, v0)::(SortedMap.insert k v rst)
  else (k,v)::rst

-- FIXME prove
axiom insert.wellFormed [DecidableLessOrder α] (k : α) (v : β) {l : List (α × β)} :
List.SortedMap l →
List.SortedMap (SortedMap.insert k v l)

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
  else (k0,v0)::(SortedMap.erase k rst)

-- FIXME prove
axiom erase.wellFormed [DecidableLessOrder α] (k : α) {l : List (α × β)} :
List.SortedMap l →
List.SortedMap (SortedMap.erase k l)

-- FIXME prove
axiom erase.stillNotIn [DecidableLessOrder α] (k : α) {v : β} {l : List (α × β)} :
l.Forall (λ (kv : α × β) => kv.snd ≠ v) →
(SortedMap.erase k l).Forall (λ (kv : α × β) => kv.snd ≠ v)


end SortedMap


end List
