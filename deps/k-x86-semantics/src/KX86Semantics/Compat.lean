-- Compatability layer between the X96Semantics support and that required by the K translation

import X86Semantics.Common

namespace x86
namespace k_x86_semantics

open mc_semantics
open mc_semantics.type
open reg
open semantics

-- Copied from Instructions.lean in X8Semantics
def least_nibble {w:Nat} (x : bv w) : bv 4 := trunc x 4
def even_parity {w:Nat} (v : bv w) : bit := prim.even_parity w v

def ssbb_overflows  {w:Nat} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.ssbb_overflows w dest src borrow
def ssub_overflows  {w:Nat} (dest : bv w) (src : bv w)                : bit := ssbb_overflows dest src bit_zero

def usbb_overflows  {w:Nat} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.usbb_overflows w dest src borrow
def usub_overflows  {w:Nat} (dest : bv w) (src : bv w)                : bit := usbb_overflows dest src bit_zero
def usub4_overflows {w:Nat} (dest : bv w) (src : bv w)                : bit := usub_overflows (least_nibble dest) (least_nibble src)

def uadc_overflows  {w:Nat} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.uadc_overflows w dest src carry
def uadc4_overflows {w:Nat} (dest : bv w) (src : bv w) (carry : bit) : bit := uadc_overflows (least_nibble dest) (least_nibble src) carry
def uadd_overflows  {w:Nat} (dest : bv w) (src : bv w)               : bit := uadc_overflows dest src bit_zero
def uadd4_overflows {w:Nat} (dest : bv w) (src : bv w)               : bit := uadd_overflows (least_nibble dest) (least_nibble src)

def sadc_overflows  {w:Nat} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.sadc_overflows w dest src carry
def sadd_overflows  {w:Nat} (dest : bv w) (src : bv w)               : bit := sadc_overflows dest src bit_zero

def pair_fst {x y : type} (e:pair x y) : x := prim.pair_fst x y e
def pair_snd {x y : type} (e:pair x y) : y := prim.pair_snd x y e

def bv_xor {w:Nat} (x : bv w) (y : bv w) : bv w := prim.bv_xor w x y
def add    {w:Nat} (x : bv w) (y : bv w) : bv w := prim.add w x y
def mul    {w:Nat} (x : bv w) (y : bv w) : bv w := prim.mul w x y
def sub    {w:Nat} (x : bv w) (y : bv w) : bv w := prim.sub w x y

def bv_and {w:Nat} (x : bv w) (y : bv w) : bv w := prim.bv_and w x y
def bv_or  {w:Nat} (x : bv w) (y : bv w) : bv w := prim.bv_or w x y

def bit_or (x : bit) (y : bit) : bit    := prim.bit_or x y

def ashr   {w j:Nat} (x : bv w) (y : bv j) : bv w := prim.sar w j x y
def lshr   {w j:Nat} (x : bv w) (y : bv j) : bv w := prim.shr w j x y
def shl    {w j:Nat} (x : bv w) (y : bv j) : bv w := prim.shl w j x y


def bv_bitcast_to_fp (fc : float_class) (x : bv fc.width) : float fc := prim.bv_bitcast_to_fp fc x

-- FIXME: check the nat is fc.width?
def fp_bitcast_to_bv {fc : float_class} (x : float fc)    (_ : Nat) : bv fc.width := prim.fp_bitcast_to_bv fc x
def fp_add           {fc : float_class} (x : float fc) (y : float fc) : float fc := prim.fp_add fc x y
def fp_sub           {fc : float_class} (x : float fc) (y : float fc) : float fc := prim.fp_sub fc x y
def fp_mul           {fc : float_class} (x : float fc) (y : float fc) : float fc := prim.fp_mul fc x y
def fp_div           {fc : float_class} (x : float fc) (y : float fc) : float fc := prim.fp_div fc x y

-- This will give strange results for counts greater than the size of
-- the input word, so it is assumed that the semantics ensures the
-- count is not too large.
--
-- rol x y = x << y | x >> (sizeof(x) - y)      a
def rol {i j : Nat} (e : bv i) (count : bv j) : bv i :=
  bv_or (shl e count) (lshr e (sub (expression.bv_nat j i) count))

def ror {i j : Nat} (e : bv i) (count : bv j) : bv i :=
  bv_or (lshr e count) (shl e (sub (expression.bv_nat j i) count))

-- unknown identifier 'clReg'
def slt {i : Nat} (x : bv i) (y : bv i) : bit := prim.slt i x y
def sgt {i : Nat} (x : bv i) (y : bv i) : bit := slt y x

def ult {i : Nat} (x : bv i) (y : bv i) : bit := prim.ult i x y
def ugt {i : Nat} (x : bv i) (y : bv i) : bit := ult y x
def ule {i : Nat} (x : bv i) (y : bv i) : bit := prim.ule i x y
def uge {i : Nat} (x : bv i) (y : bv i) : bit := ule y x

def urem {i : Nat} (x : bv i) (y : bv i) : bv i :=
  pair_snd (prim.quotRem i (uext x (2 * i)) y)

-- WARNING: the K semantics uses bit 0 as the MSB!

def load (ptr : expression (bv 64)) (n : Nat) : semantics (expression (bv (n * 8))) := eval (expression.read (bv (n * 8)) ptr)
def store (ptr : expression (bv 64)) {tp : type} (v : expression tp) (n : Nat) : semantics Unit :=
  set (lhs.write_addr ptr tp) v

-- def getRegister {t : type} (r : reg t) : semantics t := eval (expression.of_reg r)
def getRegister {t : type} (r : lhs t) : semantics (expression t) := eval (expression.of_lhs r)
def setRegister {t : type} (r : lhs t) (e : expression t) : semantics Unit := (set r e)
def notBool_ (e : bit) : bit := eq e bit_zero

def isBitSet {n : Nat} (e : bv n) (idx : Nat) : bit := 
  expression.bit_test e (expression.bv_nat n (n - idx))

def overflowFlag {n : Nat} (e1 : bv n) (e2 : bv n) (r : bv n) : bit :=
    sadd_overflows e1 e2

def parityFlag { n : Nat } (e : bv n) : bit := even_parity e
def zeroFlag { n : Nat } (e : bv n) : bit := eq e 0

def concat {i j:Nat} (x: expression (bv i)) (y : expression (bv j)) : expression (bv (i + j)) := prim.cat i j x y
def undef {tp:type} : expression tp := expression.undef tp
def isBitClear {n : Nat} (e : expression (bv n)) (b : Nat) : expression bit := 
    eq (isBitSet e b) bit_zero

-- Always called with the literal 1, but we don't assume ...
def bv1ToBool (e : bv 1) : bit := expression.bit_test e (expression.bv_nat 1 0)

-- FIXME: cl is a lhs in Common, not a concrete_reg
@[reducible]
def clReg := exact_reg _ (concrete_reg.gpreg (Fin.ofNat 1) gpreg_type.reg8l)

-- FIXME: we could maybe do this in the K backend?
def div_quotient_int8 (num : bv 16) (denom : bv 8) : bv 8 :=
  pair_fst (prim.quotRem 8 num denom)

def div_remainder_int8 (num : bv 16) (denom : bv 8) : bv 8 :=
  pair_snd (prim.quotRem 8 num denom)

def div_quotient_int16 (num : bv 32) (denom : bv 16) : bv 16 :=
  pair_fst (prim.quotRem 16 num denom)

def div_remainder_int16 (num : bv 32) (denom : bv 16) : bv 16 :=
  pair_snd (prim.quotRem 16 num denom)

def div_quotient_int32 (num : bv 64) (denom : bv 32) : bv 32 :=
  pair_fst (prim.quotRem 32 num denom)

def div_remainder_int32 (num : bv 64) (denom : bv 32) : bv 32 :=
  pair_snd (prim.quotRem 32 num denom)

def div_quotient_int64 (num : bv 128) (denom : bv 64) : bv 64 :=
  pair_fst (prim.quotRem 64 num denom)

def div_remainder_int64 (num : bv 128) (denom : bv 64) : bv 64 :=
  pair_snd (prim.quotRem 64 num denom)

-- Signed
def idiv_quotient_int8 (num : bv 16) (denom : bv 8) : bv 8 :=
  pair_fst (prim.squotRem 8 num denom)

def idiv_remainder_int8 (num : bv 16) (denom : bv 8) : bv 8 :=
  pair_snd (prim.squotRem 8 num denom)

def idiv_quotient_int16 (num : bv 32) (denom : bv 16) : bv 16 :=
  pair_fst (prim.squotRem 16 num denom)

def idiv_remainder_int16 (num : bv 32) (denom : bv 16) : bv 16 :=
  pair_snd (prim.squotRem 16 num denom)

def idiv_quotient_int32 (num : bv 64) (denom : bv 32) : bv 32 :=
  pair_fst (prim.squotRem 32 num denom)

def idiv_remainder_int32 (num : bv 64) (denom : bv 32) : bv 32 :=
  pair_snd (prim.squotRem 32 num denom)

def idiv_quotient_int64 (num : bv 128) (denom : bv 64) : bv 64 :=
  pair_fst (prim.squotRem 64 num denom)

def idiv_remainder_int64 (num : bv 128) (denom : bv 64) : bv 64 :=
  pair_snd (prim.squotRem 64 num denom)

-- def bv_to_fp (e : bv ) (mbits ebits : Nat) : fp c := 
-- def fp_to_bv 

--FIXME?
def bit_and := expression.bit_and 

def mux {tp:type} (c:bit) (t f : tp) : tp := prim.mux tp c t f

-- This is substantially different than the handwritten semantics, as we have untyped pointers.
@[reducible]
def Mem : Type := addr (bv 64)

def evaluateAddress (m : Mem) : semantics (expression (bv 64)) := eval (expression.of_addr m)
 
-- x is an immediate usually
-- assume that the int is n bits, extend to m bits.  The K here might be a bit broken?
def handleImmediateWithSignExtend (x : expression int) (n m : Nat) := prim.bv_int_sext m x

@[elabSimple]
def extractMInt {w:Nat} (x: expression (bv w)) (u:Nat) (l:Nat)
  : expression (bv ((w - u - 1) + 1 - (w - l))) := slice x (w - u - 1) (w - l)

@[elabSimple]
def extract {w:Nat} (x: expression (bv w)) (u:Nat) (l:Nat)
  : expression (bv ((w - u - 1) + 1 - (w - l))) := slice x (w - u - 1) (w - l)

-- notation `pattern` body `pat_end` := mk_pattern body

end k_x86_semantics
end x86
