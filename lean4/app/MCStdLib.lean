-- This file contains all the SMT symbols that the VCG expects to use,
-- incl. memory operations and stack bounds.

import SMTLIB.Syntax
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize

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
      match a with | (m', addr') => (m'.store_byte addr' b, SMT.bvadd addr' (SMT.bvimm 64 1));
    (List.foldl f (m, addr) bs).fst

protected
def read_bytes (m : memory) (addr : memaddr) (n : Nat) : List byte :=
    let f i := m.read_byte (SMT.bvadd addr (SMT.bvimm 64 i));
    List.map f (Nat.upto0_lt n).reverse

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

-- FIXME: the name is wrong, maybe something like MCSMTContext or something?
-- cf. `mcMemDecls`
structure MCStdLib :=
  (memOps        : forall (w : WordSize), SupportedMemType w.sort)
  (funStartRegs  : RegState)
  (blockStartMem : memory)
  (onStack       : memaddr -> bitvec 64 -> s_bool)

namespace MCStdLib

def memOpsBySort (m : MCStdLib) (s : SMT.sort) : Option (SupportedMemType s) :=
let mops := m.memOps;
match s with
| SMT.sort.bitvec 8  => some $ mops WordSize.word8
| SMT.sort.bitvec 16 => some $ mops WordSize.word16
| SMT.sort.bitvec 32 => some $ mops WordSize.word32
| SMT.sort.bitvec 64 => some $ mops WordSize.word64
| _ => none

end MCStdLib

--------------------------------------------------------------------------------
-- Memory operations

def mkMemOps : smtM (forall (w : WordSize), SupportedMemType w.sort) := do
  sm8  <- SupportedMemType.make 1;
  sm16 <- SupportedMemType.make 2;
  sm32 <- SupportedMemType.make 4;
  sm64 <- SupportedMemType.make 8;
  pure $ fun w =>  match w with
                   | WordSize.word8  => sm8
                   | WordSize.word16 => sm16
                   | WordSize.word32 => sm32
                   | WordSize.word64 => sm64

--------------------------------------------------------------------------------
-- Stack properties

-- | @defineRangeCheck nm low high@ introduces the definition for a
-- function named @nm@ that takes an address @a@ and size @sz@, and
-- checks that @[a..a+sz)@ is in @[low..high)@ and that @a+sz@ does not overflow.
def defineRangeCheck (name : String) (low : memaddr) (high : memaddr) 
  : smtM (memaddr -> bitvec 64 -> s_bool) := do
  eName <- SMT.freshSymbol "e";
  SMT.define_fun name [SMT.sort.bitvec 64, SMT.sort.bitvec 64] SMT.sort.smt_bool $ fun addr sz => 
    SMT.smt_let eName (SMT.bvadd addr sz) $ fun e =>
      SMT.and (SMT.bvule low addr) 
         (SMT.and (SMT.bvule addr e)
                  (SMT.bvule e high))

-- | Defines a predicate @(not_in_stack_range a sz)@ that holds if @a + sz@
-- does not overflow and @[a..a+sz)@ does not overlap with the
-- range @[stack_alloc_min..stack_max)@.
--
-- See `mcMemDecls` for details about `stack_alloc_max` and `stack_max`.
def defineNotInStackRange (stack_alloc_min : memaddr) (stack_max : memaddr)
  : smtM (memaddr -> bitvec 64 -> s_bool) := do
  eName <- SMT.freshSymbol "e";
  SMT.define_fun "not_in_stack_range" [SMT.sort.bitvec 64, SMT.sort.bitvec 64] SMT.sort.smt_bool $
    fun addr sz => 
      SMT.smt_let eName (SMT.bvadd addr sz) $ fun e =>
        SMT.and (SMT.bvule addr e)
           (SMT.or (SMT.bvule e stack_alloc_min)
                   (SMT.bvule stack_max addr))


-- FIXME: define
-- def defineMCOnlyStackRange (on_stack : memaddr -> bitvec 64 -> s_bool) (allocas : ... )
--   : smtM (memaddr -> bitvec 64 -> s_bool) := do
--   eName <- SMT.freshSymbol "e";
--   SMT.define_fun "mc_only_stack_range" [SMT.sort.bitvec 64, SMT.sort.bitvec 64] SMT.sort.smt_bool $
--     fun addr sz => 
--       SMT.smt_let eName (SMT.bvadd addr sz) $ fun e =>
--         SMT.and (on_stack addr sz)
--                      -- ++ [ isDisjoint ("a", "e") (allocaMCBaseVar nm, allocaMCEndVar nm)
--                      --    | a <- allocas
--                      --    , let nm = Ann.allocaIdent a
--                      --    ]


-- nbits should be > 0, nbits should be a power of 2
def isAligned {n : Nat} (v : bitvec n) (nbits : Nat) : s_bool := 
  SMT.eq (SMT.bvand v (SMT.bvimm _ (nbits - 1))) (SMT.bvimm _ 0)

namespace MCStdLib

-- FIXME
def rsp_idx : Fin 16 := 4

-- FIXME: some of this is not used in the absence of allocas
def make (ip : Nat) (pageSize : Nat) (guardPageCount : Nat) : smtM MCStdLib := do
  -- FIXME: add checks
  memOps <- mkMemOps;

  funStartRegs <- RegState.declare_const "fnstart_" ip;
  let stackHighTerm := funStartRegs.get_gpreg rsp_idx;

  blockStartMem <- SMT.declare_fun "init_mem" [] memory_t;

  let guardSize := pageSize * guardPageCount;
  stack_alloc_min <- SMT.declare_fun "stack_alloc_min" [] (SMT.sort.bitvec 64);
  SMT.assert $ isAligned stack_alloc_min pageSize;
  SMT.assert $ SMT.bvult (SMT.bvimm _ guardSize) stack_alloc_min;

  stack_guard_min <- SMT.define_fun "stack_guard_min" [] (SMT.sort.bitvec 64) $
                     SMT.bvsub stack_alloc_min (SMT.bvimm _ guardSize);

  SMT.assert $ SMT.bvult stack_guard_min stack_alloc_min;

  -- Declare the upper bound on stack address.
  stack_max <- SMT.declare_fun "stack_max" [] (SMT.sort.bitvec 64);
  SMT.assert $ isAligned stack_max pageSize;   

  -- Assert stack_alloc_min < stack_max
  SMT.assert $ SMT.bvult stack_alloc_min stack_max;

  -- Assert RSP is between stack_alloc_min and stack_max - return address size
  SMT.assert $ SMT.bvule stack_alloc_min stackHighTerm;
  SMT.assert $ SMT.bvule stackHighTerm (SMT.bvsub stack_max (SMT.bvimm _ 8));

  -- Define check to assert stack is in given range
  onStack <- defineRangeCheck "on_stack" stack_guard_min stack_max;

  -- Declare not in stack that asserts a range is not on the stack.
  notInStack <- defineNotInStackRange stack_alloc_min stack_max;

  -- Assert that stack pointer is at least 8 below stack high
  SMT.assert $ SMT.bvult stackHighTerm (SMT.bvsub stack_max (SMT.bvimm _ 8));
  -- High water stack pointer includes 8 bytes for return address.
  -- The return address top must be aligned to a 16-byte boundary.
  SMT.assert $ isAligned (SMT.bvadd stackHighTerm (SMT.bvimm _ 8)) 16;
  -- ++ concatMap allocaMCBaseEndDecls allocas -- FIXME
  -- Declare mcOnlyStackRange
  -- defineMCOnlyStackRange onStack
  pure { memOps       := memOps
       , funStartRegs := funStartRegs  
       , blockStartMem := blockStartMem
       , onStack      := onStack
       }


end MCStdLib

end vcg
end x86
