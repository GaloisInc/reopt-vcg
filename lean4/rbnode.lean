namespace RBNode
variable {α : Type _}
variable {β : Type _}
variable (lt : α → α → Bool)

def ofList' : RBNode α (λ_, β) → List (α × β) → RBNode α (λ_, β)
| l [] := l
| l ((k,v) :: r) := ofList' (l.insert lt k v) r


def ofList (l:List (α × β)) : RBNode α (λ_, β) := ofList' lt leaf l


section
variable {A:Type _}
variable {B:A → Type _}
variable {σ : Type _}
variable (f : Π(k:A), B k → σ → σ)

def foldRight : RBNode A B → σ → σ
| RBNode.leaf s := s
| (RBNode.node _ l k v r) s := foldRight l (f k v (foldRight r s))

end

end RBNode
