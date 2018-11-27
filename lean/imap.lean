/- A simple interval map -/

structure {u v} data.imap.imap_entry (k : Type u) (val : Type v) : Type (max u v) := 
  (start : k) 
  (extent : k)
  (value : val)

def {u v} data.imap (k : Type u) (val : Type v) := list (data.imap.imap_entry k val)

namespace data.imap
section

universes u v
parameters {k : Type u} {val : Type v} [has_add k] [has_lt k] [has_le k] 
           [decidable_rel ((<) : k -> k -> Prop)]
           [decidable_rel ((≤) : k -> k -> Prop)]
           [decidable_eq k] -- redundant?

def in_entry (key : k) (e : imap_entry k val) : bool :=
  e.start ≤ key ∧ key < (e.start + e.extent)

def lookup (key : k) : data.imap k val -> option (k × val)
  | [] := none
  | (e :: m) := if in_entry key e 
                then some (e.start, e.value) 
                else lookup m

-- FIXME: add overlap check
def insert (start : k) (extent : k) (value : val) : data.imap k val -> data.imap k val :=
  λm, { start := start, extent := extent, value := value } :: m

end 
end data.imap
