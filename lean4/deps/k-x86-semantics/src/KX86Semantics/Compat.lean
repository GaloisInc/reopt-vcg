-- Compatability layer between the X96Semantics support and that required by the K translation

import X86Semantics.Common

namespace x86
namespace k_x86_semantics

open mc_semantics
open mc_semantics.type
open reg
open semantics

-- Copied from Instructions.lean in X8Semantics
def least_nibble {w:nat_expr} (x : bv w) : bv 4 := trunc x 4
def even_parity {w:nat_expr} (v : bv w) : bit := prim.even_parity w v

def ssbb_overflows  {w:nat_expr} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.ssbb_overflows w dest src borrow
def ssub_overflows  {w:nat_expr} (dest : bv w) (src : bv w)                : bit := ssbb_overflows dest src bit_zero

def usbb_overflows  {w:nat_expr} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.usbb_overflows w dest src borrow
def usub_overflows  {w:nat_expr} (dest : bv w) (src : bv w)                : bit := usbb_overflows dest src bit_zero
def usub4_overflows {w:nat_expr} (dest : bv w) (src : bv w)                : bit := usub_overflows (least_nibble dest) (least_nibble src)

def uadc_overflows  {w:nat_expr} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.uadc_overflows w dest src carry
def uadc4_overflows {w:nat_expr} (dest : bv w) (src : bv w) (carry : bit) : bit := uadc_overflows (least_nibble dest) (least_nibble src) carry
def uadd_overflows  {w:nat_expr} (dest : bv w) (src : bv w)               : bit := uadc_overflows dest src bit_zero
def uadd4_overflows {w:nat_expr} (dest : bv w) (src : bv w)               : bit := uadd_overflows (least_nibble dest) (least_nibble src)

def sadc_overflows  {w:nat_expr} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.sadc_overflows w dest src carry
def sadd_overflows  {w:nat_expr} (dest : bv w) (src : bv w)               : bit := sadc_overflows dest src bit_zero

def bv_xor {w:nat_expr} (x : bv w) (y : bv w) : bv w := prim.bv_xor w x y
def add    {w:nat_expr} (x : bv w) (y : bv w) : bv w := prim.bv_xor w x y

-- WARNING: the K semantics uses bit 0 as the MSB!

def load (ptr : expression (bv 64)) (n : Nat) : semantics (expression (bv (n * 8))) := eval (expression.read (bv (n * 8)) ptr)
def store (ptr : expression (bv 64)) {tp : type} (v : expression tp) (n : Nat) : semantics Unit :=
  set (lhs.write_addr ptr tp) v

def getRegister {t : type} (r : reg t) : semantics t := eval (expression.of_reg r)
def setRegister {t : type} (r : lhs t) (e : expression t) : semantics Unit := (set r e)
def notBool_ (e : bit) : bit := eq e bit_zero

def isBitSet {n : nat_expr} (e : bv n) (idx : nat_expr) : bit := 
  expression.bit_test e (expression.bv_nat n (n - idx))

def overflowFlag {n : nat_expr} (e1 : bv n) (e2 : bv n) (r : bv n) : bit :=
    sadd_overflows e1 e2

def parityFlag { n : nat_expr } (e : bv n) : bit := even_parity e
def zeroFlag { n : nat_expr } (e : bv n) : bit := eq e 0
def concat {i j:nat_expr} (x: bv i) (y : bv j) : bv (i + j) := prim.cat i j x y
def undef {tp:type} : expression tp := expression.undef tp

-- This is substantially different than the handwritten semantics, as we have untyped pointers.
@[reducible]
def Mem : Type := expression (bv 64)

def evaluateAddress (m : Mem) : semantics (bv 64) := eval m
 
-- x is an immediate usually
def handleImmediateWithSignExtend (x : int) (n m : nat_expr) := prim.bv_int_sext n x

def extract {w:Nat} (x: expression (bv (nat_expr.lit w))) (u:Nat) (l:Nat)
  : expression (bv (nat_expr.lit ((w - u - 1) + 1 - (w - l)))) := slice x (w - u - 1) (w - l)

notation `pattern` body `pat_end` := mk_pattern body

end k_x86_semantics
end x86
