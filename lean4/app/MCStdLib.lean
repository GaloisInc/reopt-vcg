
import SMTLIB.Syntax
import ReoptVCG.VCGBackend

namespace x86
namespace vcg

open SMT (sort term smtM command)

abbrev memory_t := SMT.sort.array (SMT.sort.bitvec 64) (SMT.sort.bitvec 8)
def memory := term memory_t

-------------------------------------------------------
-- MC memory operations
-------------------------------------------------------
namespace memory

protected
def read_byte (mem : memory) (addr : memaddr) : byte := SMT.select _ _ mem addr
protected
def store_byte (mem : memory) (addr : memaddr) (b : byte) : memory := SMT.store _ _ mem addr b

protected
def store_bytes (m : memory) (addr : memaddr) (bs : List byte) : memory := 
    let f (a : memory × memaddr) b : memory × memaddr := 
      match a with | (m', addr') => (m.store_byte addr' b, SMT.bvadd addr' (SMT.bvimm 64 1));
    (List.foldl f (m, addr) bs).fst

protected
def read_bytes (m : memory) (addr : memaddr) (n : Nat) : List byte :=
    let f i := m.read_byte (SMT.bvadd addr (SMT.bvimm 64 i));
    List.map f (Nat.upto0_lt n)

def store_word {n : Nat} (m : memory) (addr : memaddr) (b : bitvec (8 * n)) : memory := 
  m.store_bytes addr (b.split_list 8).reverse 

def read_word (n : Nat) (m : memory) (addr : memaddr) : bitvec (8 * n) :=
  let bs := m.read_bytes addr n;
  let w  : bitvec (8 * bs.length) := bitvec.concat_list bs;
  let pf : 8 * bs.length = 8 * n := sorryAx _;
  bitvec.cong pf w

end memory

structure SupportedMemType (s : SMT.sort) :=
  (readMem  : memory -> memaddr -> SMT.term s)
  (writeMem : memory -> memaddr -> SMT.term s -> memory)

namespace SupportedMemType

def make (nBytes : Nat) : smtM (SupportedMemType (SMT.sort.bitvec (8 * nBytes))) := do
  let n := 8 * nBytes;
  rm <- SMT.define_fun ("mem_read" ++ repr n) [memory_t, SMT.sort.bitvec 64] (SMT.sort.bitvec n) 
           (memory.read_word nBytes);
  wm <- SMT.define_fun ("mem_write" ++ repr n) [memory_t, SMT.sort.bitvec 64, SMT.sort.bitvec n] memory_t
           memory.store_word;
  pure { readMem := rm, writeMem := wm }

end SupportedMemType

def mkMemOps : smtM (forall (s : sort), Option (SupportedMemType s)) := do 
  sm8  <- SupportedMemType.make 1;
  sm16 <- SupportedMemType.make 2;
  sm32 <- SupportedMemType.make 4;
  sm64 <- SupportedMemType.make 8;
  pure $ fun s =>  match s with
                   | SMT.sort.bitvec 8  => some sm8
                   | SMT.sort.bitvec 16 => some sm16
                   | SMT.sort.bitvec 32 => some sm32
                   | SMT.sort.bitvec 64 => some sm64
                   | _                  => none

end vcg
end x86
