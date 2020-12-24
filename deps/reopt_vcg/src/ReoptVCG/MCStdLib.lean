-- This file contains all the SMT symbols that the VCG expects to use,
-- incl. memory operations and stack bounds.

import SmtLib.Smt
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import ReoptVCG.Types

namespace x86
namespace vcg

open Smt (SmtSort SmtSort.bool SmtSort.bitvec SmtSort.array Term SmtM Command)
open ReoptVCG

-------------------------------------------------------
-- MC memory operations
-------------------------------------------------------
namespace memory

protected
def read_byte (mem : memory) (addr : memaddr) : byte := Smt.select _ _ mem addr
protected
def store_byte (mem : memory) (addr : memaddr) (b : byte) : memory := Smt.store _ _ mem addr b

protected
def store_bytes (m : memory) (addr : memaddr) (bs : List byte) : memory := 
    let f : (memory × memaddr) → byte → (memory × memaddr) := λ a b =>
      match a with | (m', addr') => (m'.store_byte addr' b, Smt.bvadd addr' (Smt.bvimm 64 1))
    (bs.foldl f (m, addr)).fst

protected
def read_bytes (m : memory) (addr : memaddr) (n : Nat) : List byte :=
    let f := λ i => m.read_byte (Smt.bvadd addr (Smt.bvimm 64 i))
    (Nat.upto0_lt n).reverse.map f

def store_word {n : Nat} (m : memory) (addr : memaddr) (b : bitvec (8 * n)) : memory := 
  m.store_bytes addr (b.split_list 8).reverse 

def read_word (n : Nat) (m : memory) (addr : memaddr) : bitvec (8 * n) :=
  let bs := m.read_bytes addr n
  let w  : bitvec (8 * bs.length) := bitvec.concat_list bs
  let pf : 8 * bs.length = 8 * n := sorryAx _
  bitvec.cong pf w

end memory

namespace SupportedMemType

def make (nBytes : Nat) : SmtM (SupportedMemType (SmtSort.bitvec (8 * nBytes))) := do
  let n := 8 * nBytes
  let rm ← Smt.defineFun ("mem_readbv" ++ repr n) [memory_t, SmtSort.bitvec 64] (SmtSort.bitvec n) 
                          (memory.read_word nBytes)
  let wm ← Smt.defineFun ("mem_writebv" ++ repr n) [memory_t, SmtSort.bitvec 64, SmtSort.bitvec n] memory_t
                          memory.store_word
  pure { readMem := rm, writeMem := wm }

end SupportedMemType


namespace MCStdLib

def memOpsBySort (m : MCStdLib) (s : SmtSort) : Option (SupportedMemType s) :=
let mops := m.memOps
match s with
| SmtSort.bitvec 8  => some $ mops WordSize.word8
| SmtSort.bitvec 16 => some $ mops WordSize.word16
| SmtSort.bitvec 32 => some $ mops WordSize.word32
| SmtSort.bitvec 64 => some $ mops WordSize.word64
| _ => none

end MCStdLib

--------------------------------------------------------------------------------
-- Memory operations

def mkMemOps : SmtM (forall (w : WordSize), SupportedMemType w.sort) := do
  let sm8  ← SupportedMemType.make 1
  let sm16 ← SupportedMemType.make 2
  let sm32 ← SupportedMemType.make 4
  let sm64 ← SupportedMemType.make 8
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
  : SmtM (memaddr -> bitvec 64 -> s_bool) := do
  let eName ← Smt.freshSymbol "e"
  Smt.defineFun name [SmtSort.bitvec 64, SmtSort.bitvec 64] SmtSort.bool $ fun addr sz => 
    Smt.smtLet eName (Smt.bvadd addr sz) $ fun e =>
      Smt.and (Smt.bvule low addr) 
         (Smt.and (Smt.bvule addr e)
                  (Smt.bvule e high))

-- | Defines a predicate @(not_in_stack_range a sz)@ that holds if @a + sz@
-- does not overflow and @[a..a+sz)@ does not overlap with the
-- range @[stack_alloc_min..stack_max)@.
--
-- See `mcMemDecls` for details about `stack_alloc_max` and `stack_max`.
def defineNotInStackRange (stack_alloc_min : memaddr) (stack_max : memaddr)
  : SmtM (memaddr -> bitvec 64 -> s_bool) := do
  let eName ← Smt.freshSymbol "e"
  Smt.defineFun "not_in_stack_range" [SmtSort.bitvec 64, SmtSort.bitvec 64] SmtSort.bool $
    fun addr sz => 
      Smt.smtLet eName (Smt.bvadd addr sz) $ fun e =>
        Smt.and (Smt.bvule addr e)
           (Smt.or (Smt.bvule e stack_alloc_min)
                   (Smt.bvule stack_max addr))


def defineIsInMCOnlyStackRange
  (onStack : (memaddr -> bitvec 64 -> s_bool))
  (allocas : Std.RBMap LocalIdent AllocaMC (λ x y => x < y))
  : SmtM (memaddr -> bitvec 64 -> s_bool) := do
  let eName ← Smt.freshSymbol "e"
  Smt.defineFun "is_in_mc_only_stack_range" [SmtSort.bitvec 64, SmtSort.bitvec 64] SmtSort.bool $
    fun addr sz =>
      Smt.smtLet eName (Smt.bvadd addr sz) $ fun e =>
        Smt.all $
          (onStack addr sz)::(allocas.fold
                               (λ ps _ a =>
                                  (isDisjoint addr e a.baseAddress a.endAddress)::ps)
                               [])


-- nbits should be > 0, nbits should be a power of 2
def isAligned {n : Nat} (v : bitvec n) (nbits : Nat) : s_bool := 
  Smt.eq (Smt.bvand v (Smt.bvimm _ (nbits - 1))) (Smt.bvimm _ 0)


/- @allocaMCBaseEndDecls a@ introduces variables for defining the
    extent in the machine code stack of an LLVM alloca. -/
def allocaMCBaseEndDecls (a : AllocaAnn) (stackHighTerm : bitvec 64) : SmtM AllocaMC := do
  let nm : String := a.ident.name
  let baseNm : String := "alloca_" ++ nm ++ "_mc_base"
  let baseAddr : bitvec 64 := Smt.bvimm 64 a.binOffset
  let endNm := "alloca_" ++ nm ++ "_mc_end"
  let endAddr : bitvec 64 := Smt.bvsub baseAddr (Smt.bvimm 64 a.size)
  -- Define machine code base for allocation.
  let baseTerm ← Smt.defineFun baseNm [] (SmtSort.bitvec 64) $ Smt.bvsub stackHighTerm baseAddr
  let endTerm ← Smt.defineFun endNm [] (SmtSort.bitvec 64) $ Smt.bvsub stackHighTerm endAddr
  -- Introduce predicate to check machine-code addresses.
  let predNm : String := "mcaddr_in_alloca_" ++ nm
  let rangeCheck ← defineRangeCheck predNm baseTerm endTerm
  pure {baseAddress := baseTerm,
        endAddress  := endTerm,
        isInAlloca  := rangeCheck}

namespace MCStdLib

-- FIXME
def rsp_idx : Fin 16 := Fin.ofNat 4


def make (ip : Nat) (pageSize : Nat) (guardPageCount : Nat) (allocas : AllocaAnnMap) : SmtM MCStdLib := do
  -- FIXME: add checks
  let memOps ← mkMemOps

  let funStartRegs ← RegState.declare_const "fnstart_" ip
  let stackHighTerm := funStartRegs.get_gpreg rsp_idx

  let blockStartMem ← Smt.declareFun "init_mem" [] memory_t

  let guardSize := pageSize * guardPageCount
  let stack_alloc_min ← Smt.declareFun "stack_alloc_min" [] (SmtSort.bitvec 64)
  Smt.assert $ isAligned stack_alloc_min pageSize
  Smt.assert $ Smt.bvult (Smt.bvimm _ guardSize) stack_alloc_min

  let stack_guard_min ← Smt.defineFun "stack_guard_min" [] (SmtSort.bitvec 64) $
                           Smt.bvsub stack_alloc_min (Smt.bvimm _ guardSize)

  Smt.assert $ Smt.bvult stack_guard_min stack_alloc_min

  -- Declare the upper bound on stack address.
  let stack_max ← Smt.declareFun "stack_max" [] (SmtSort.bitvec 64)
  Smt.assert $ isAligned stack_max pageSize   

  -- Assert stack_alloc_min < stack_max
  Smt.assert $ Smt.bvult stack_alloc_min stack_max

  -- Assert RSP is between stack_alloc_min and stack_max - return address size
  Smt.assert $ Smt.bvule stack_alloc_min stackHighTerm
  Smt.assert $ Smt.bvule stackHighTerm (Smt.bvsub stack_max (Smt.bvimm _ 8))

  -- Define check to assert stack is in given range
  let onStack ← defineRangeCheck "on_stack" stack_guard_min stack_max

  -- Declare not in stack that asserts a range is not on the stack.
  let notInStack ← defineNotInStackRange stack_alloc_min stack_max

  -- Assert that stack pointer is at least 8 below stack high
  Smt.assert $ Smt.bvult stackHighTerm (Smt.bvsub stack_max (Smt.bvimm _ 8))

  -- High water stack pointer includes 8 bytes for return address.
  -- The return address top must be aligned to a 16-byte boundary.
  Smt.assert $ isAligned (Smt.bvadd stackHighTerm (Smt.bvimm _ 8)) 16

  let allocaMap ← allocas.foldM
                  (λ (m : Std.RBMap LocalIdent AllocaMC (λ x y => x<y))
                    (ident : LocalIdent)
                    (alloc : AllocaAnn) => do
                    let mcAlloc ← allocaMCBaseEndDecls alloc stackHighTerm
                    pure $ m.insert ident mcAlloc)
               Std.RBMap.empty
  -- Declare isInMCOnlyStackRange
  let isInMCOnlyStackRange ← defineIsInMCOnlyStackRange onStack allocaMap
  pure { memOps        := memOps
       , funStartRegs  := funStartRegs
       , blockStartMem := blockStartMem
       , onStack       := onStack
       , allocaMap     := allocaMap
       , notInStack    := notInStack
       , isInMCOnlyStackRange := isInMCOnlyStackRange
       }


end MCStdLib

end vcg
end x86