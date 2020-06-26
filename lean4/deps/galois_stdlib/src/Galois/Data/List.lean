namespace List

section
universes u v
variables {α : Type u} {β : Type v}

def joinMap (f : α → List β) : List α → List β
| []      => []
| a :: as => (f a) ++ joinMap as

end

end List
