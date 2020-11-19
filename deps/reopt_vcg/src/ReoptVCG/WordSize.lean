
import SmtLib.Smt

open Smt (SmtSort SmtSort.bitvec)

inductive WordSize
| word8  : WordSize
| word16 : WordSize
| word32 : WordSize
| word64 : WordSize

namespace WordSize

def bytes : WordSize → Nat
| word8  => 1
| word16 => 2
| word32 => 4
| word64 => 8


/- Bit width (i.e., the nominal width) -/
def bits (w:WordSize) : Nat := 8 * w.bytes

def sort (w:WordSize) : SmtSort := SmtSort.bitvec w.bits

def fromNat : Nat → Option WordSize
| 8  => some word8
| 16 => some word16
| 32 => some word32
| 64 => some word64
| _  => none

end WordSize
