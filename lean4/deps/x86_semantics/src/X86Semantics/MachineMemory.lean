
import Galois.Data.Bitvec
import X86Semantics.BufferMap

@[reducible]
def memaddr  := bitvec 64

@[reducible]
def byte := UInt8

-- -- FIXME: maybe Nat is more efficient here?
-- inductive region 
--   | has_contents : buffer byte -> region
--   | all_zeroes   : Nat -> region

@[reducible]
def init_memory := buffer_map memaddr (fun k k' => Int.ofNat (bitvec.to_nat k) - Int.ofNat (bitvec.to_nat k'))

@[reducible]
def mutable_memory := RBMap memaddr byte (fun x y => decide (bitvec.ult x y)) -- FIXME: byte?

structure memory :=
  ( init : init_memory )
  ( mem  : mutable_memory ) 

-- namespace array

-- universes u v

-- -- FIXME: Maybe make buffer a functor?
-- def map' {a : Type u} {b : Type v} {n : Nat} (f : a -> b) (a : array n a) : array n b
--   := d_array.mk (fun (i : fin n) => f (a.read i))

-- end array

namespace memory

@[reducible]
def region := ByteArray

-- FIXME: buffer/array don't have the usual map 
-- def char_buffer_to_region (b : char_buffer) : region :=
--   -- There doesn't seem to be a nicer way of doing this?
--   array.to_buffer (array.map' (fun (c : char) => bitvec.of_nat _ c.val) b.to_array)

/- Construction -/
def empty : memory := memory.mk buffer_map.empty (mkRBMap _ _ (fun x y => decide (bitvec.ult x y)))

def from_init (i : init_memory) : memory := { empty with init := i }

/- Reading and writing -/

def store_bytes (m : memory) (addr : memaddr) (bs : List byte) : memory := 
  { m with mem := (List.foldl (fun (v : mutable_memory × memaddr) b => (RBMap.insert v.fst v.snd b, v.snd + 1)) (m.mem, addr) bs).fst }
 
-- [0 ..< x]
def upto0_lt_helper : ∀(m : Nat), List Nat -> List Nat
  | 0,            acc => acc
  | (Nat.succ n), acc => upto0_lt_helper n (n :: acc)

def upto0_lt (m : Nat) : List Nat := upto0_lt_helper m []

namespace upto0_lt

-- lemma length_is_n' : ∀{n : Nat} {acc : list Nat}
--   , (upto0_lt_helper n acc).length = n + acc.length :=
-- begin
--   intros n, 
--   induction n,
--   { intro, simp, refl },
--   { intro, simp [upto0_lt_helper, n_ih]
--   , simp [nat.succ_add_eq_succ_add, nat.add_assoc, nat.add_comm, nat.add_left_comm] }
-- end

-- lemma length_is_n : ∀{n : Nat}, (upto0_lt n).length = n :=
-- begin
--   intros n, 
--   unfold upto0_lt, 
--   apply length_is_n',
-- end

end upto0_lt

-- lemma {u v} option.bind.is_some {a : Type u} {b : Type v} {v : option a} {f : a -> option b} {x : b}:
--   option.bind v f = some x -> (∃v', v = some v' ∧ f v' = some x) :=
-- begin
--   cases v,
--   { simp [option.bind] },
--   { simp [option.bind] }
-- end

-- lemma list.mmap.length_at_option {a b : Type} {f : a -> option b} : ∀{xs : list a} {ys : list b},
--   list.mmap f xs = some ys -> xs.length = ys.length :=
-- begin
--   intros,
--   induction xs generalizing ys,
--   { simp [list.mmap, option_t.pure, return, pure] at a_1, rw <- a_1, refl},
--   { simp, simp [list.mmap, bind, option.bind] at a_1, 
--     destruct a_1, intros, 
--     destruct h, simp, intros, simp [return, pure] at a_3,
--     rw (xs_ih a_2), rw <- a_3, simp [list.length]
--   }
-- end

def bitvec.to_byte (b : bitvec 8) : UInt8 := UInt8.ofNat b.to_nat
def UInt8.to_bitvec (v : UInt8) : bitvec 8 := bitvec.of_nat 8 v.toNat

def read_byte (m : memory) (addr : memaddr) : Option byte :=
  m.mem.find? addr <|> m.init.lookup addr

def read_bytes (m : memory) (addr : memaddr) (n : Nat) : Option (List byte) :=
   List.mapM (fun n => read_byte m (addr + bitvec.of_nat 64 n)) (upto0_lt n)

-- lemma read_bytes_length {mem : memory} {addr : memaddr} {n : Nat} {bs : list (bitvec 8)}
--   : read_bytes mem addr n = some bs -> bs.length = n :=
-- begin
--   intros H,
--   simp [read_bytes] at H,
--   have H' := list.mmap.length_at_option H,
--   simp [upto0_lt.length_is_n] at H',
--   rw H'
-- end

def store_word {n : Nat} (m : memory) (addr : memaddr) (b : bitvec (8 * n)) : memory := 
  m.store_bytes addr (List.map bitvec.to_byte (b.split_list 8)).reverse 

def read_word (m : memory) (addr : memaddr) (n : Nat) : Option (bitvec (8 * n)) :=
  (fun (bs : List byte) => bitvec.concat_list (List.map UInt8.to_bitvec bs).reverse (8 * n)) <$> m.read_bytes addr n

end memory
