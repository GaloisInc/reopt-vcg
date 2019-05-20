/- A map from indexes onto buffers -/
import data.buffer

structure {u v} buffer_map.entry (k : Type u) (val : Type v) : Type (max u v) := 
  (start : k) 
  (value : buffer val)

-- distance here is essentially subtraction.  distance k k' < 0 iff k < k'
structure {u v} buffer_map (k : Type u) (val : Type v) (distance : k -> k -> ℤ) :=
  (entries : list (buffer_map.entry k val) )

namespace buffer_map
section

universes u v

parameters {k : Type u} {val : Type v} {distance : k -> k -> ℤ}

/- construction -/
def empty : buffer_map k val distance := buffer_map.mk distance []

/- lookup -/
def in_entry (key : k) (e : entry k val) : Prop :=
  distance key e.start ≥ 0 ∧ int.nat_abs (distance key e.start) < e.value.size

def entry_idx (key : k) (e : entry k val) : option (fin e.value.size) :=
  if H : distance key e.start ≥ 0 ∧ int.nat_abs (distance key e.start) < e.value.size
  then some (fin.mk _ H.right) 
  else none

protected
def lookup' : list (buffer_map.entry k val) -> k -> option val
  | [] _         := none
  | (e :: m) key := 
    match entry_idx key e with
    | none       := lookup' m key
    | (some idx) := some (e.value.read idx)
    end

def lookup (m : buffer_map k val distance) := lookup' m.entries

protected
def lookup_buffer' : list (buffer_map.entry k val) -> k -> option (k × buffer val)
  | [] _         := none
  | (e :: m) key := 
    match entry_idx key e with
    | none       := lookup_buffer' m key
    | (some idx) := some (e.start, e.value)
    end

def lookup_buffer (m : buffer_map k val distance) := lookup_buffer' m.entries

/- insertion -/

-- FIXME: add overlap check
def insert (m : buffer_map k val distance) (start : k) (value : buffer val) : buffer_map k val distance :=
  buffer_map.mk distance ({ start := start, value := value } :: m.entries)

end 

end buffer_map

section 

universes u v
parameters {k : Type u} {val : Type v} {distance : k -> k -> ℤ} [has_repr k]

instance : has_repr (buffer_map.entry k val) :=
  ⟨λe, "( [" ++ repr e.start ++ " ..+ " ++ repr e.value.size ++ "]" /-" -> " ++ has_repr.repr e.value -/ ++ ")"⟩                  

instance : has_repr (buffer_map k val distance) := ⟨λm, repr m.entries ⟩

end
