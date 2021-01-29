/- A map from indexes onto buffers, specialised to bytes -/
structure buffer_map.entry.{u} (k : Type u) : Type u := 
  (start : k) 
  (value : ByteArray)

-- distance here is essentially subtraction.  distance k k' < 0 iff k < k'
structure buffer_map.{u} (k : Type u) (distance : k -> k -> Int) :=
  (entries : List (buffer_map.entry k))

namespace buffer_map
section

universe u

variable {k : Type u} {distance : k -> k -> Int}

/- construction -/
def empty : buffer_map k distance := buffer_map.mk []

/- lookup -/
def in_entry (key : k) (e : entry k) : Prop :=
  distance key e.start ≥ 0 ∧ Int.natAbs (distance key e.start) < e.value.size

def entry_idx (key : k) (e : entry k) : Option (Fin e.value.size) :=
  if H : distance key e.start ≥ 0 ∧ Int.natAbs (distance key e.start) < e.value.size
  then some (Fin.mk _ H.right) 
  else none

protected
def lookup' : List (buffer_map.entry k) -> k -> Option UInt8
  | [], _         => none
  | (e :: m), key => 
    match @entry_idx k distance key e with
    | none       => buffer_map.lookup' m key
    | (some idx) => some (e.value.get! idx.val)

def lookup (m : buffer_map k distance) := @buffer_map.lookup' k distance m.entries

protected
def lookup_buffer' : List (buffer_map.entry k) -> k -> Option (k × ByteArray)
  | [], _         => none
  | (e :: m), key => 
    match @entry_idx k distance key e with
    | none       => buffer_map.lookup_buffer' m key
    | (some idx) => some (e.start, e.value)

def lookup_buffer (m : buffer_map k distance) := @buffer_map.lookup_buffer' k distance m.entries

/- insertion -/

-- FIXME: add overlap check
def insert (m : buffer_map k distance) (start : k) (value : ByteArray) : buffer_map k distance :=
  buffer_map.mk ({ start := start, value := value } :: m.entries)

end 

end buffer_map

section 

universes u
variable {k : Type u} {distance : k -> k -> Int} [Repr k]

-- FIXME: behave wrt prec
instance : Repr (buffer_map.entry k) :=
  ⟨fun e _n => Std.Format.text ("( [" ++ reprStr e.start ++ " ..+ " ++ reprStr e.value.size ++ "]") /-" -> " ++ has_repr.repr e.value -/ ++ ")"⟩                  

-- FIXME: behave wrt prec
instance : Repr (buffer_map k distance) := ⟨fun m _n => repr m.entries ⟩

end
