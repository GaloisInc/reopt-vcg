-- Compatability layer between the X96Semantics support and that required by the K translation

import X86Semantics.Common

namespace x86
namespace k_x86_semantics

open mc_semantics
open mc_semantics.type
open reg
open semantics
open float_class

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
def fp_bitcast_to_bv {fc : float_class} (x : expression (float fc))    (_ : Nat) : bv fc.width := prim.fp_bitcast_to_bv fc x
def int_convert_to_fp (fc : float_class) (n : Nat) (x : expression (bv n)) : float fc := prim.int_convert_to_fp fc n x 

def fp_add           {fc : float_class} (x y : expression (float fc)) : expression (float fc) := prim.fp_add fc x y
def fp_sub           {fc : float_class} (x y : expression (float fc)) : expression (float fc) := prim.fp_sub fc x y
def fp_mul           {fc : float_class} (x y : expression (float fc)) : expression (float fc) := prim.fp_mul fc x y
def fp_div           {fc : float_class} (x y : expression (float fc)) : expression (float fc) := prim.fp_div fc x y
def fp_lt            {fc : float_class} (x y : expression (float fc)) : expression bit      := prim.fp_lt  fc x y
def fp_le            {fc : float_class} (x y : expression (float fc)) : expression bit      := prim.fp_le  fc x y

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
  expression.bit_test e (expression.bv_nat n (n - idx - 1))

def overflowFlag {n : Nat} (e1 : bv n) (e2 : bv n) (r : bv n) : bit :=
    sadd_overflows e1 e2

def parityFlag { n : Nat } (e : bv n) : bit := even_parity e
def zeroFlag { n : Nat } (e : bv n) : bit := eq e 0

def concat {i j:Nat} (x: expression (bv i)) (y : expression (bv j)) : expression (bv (i + j)) := prim.cat i j x y
def undef {tp:type} : expression tp := expression.undef tp
def isBitClear {n : Nat} (e : expression (bv n)) (b : Nat) : expression bit := 
    eq (isBitSet e b) bit_zero

def mux {tp:type} (c:expression bit) (t f : expression tp) : expression tp := prim.mux tp c t f

-- Always called with the literal 1, but we don't assume ...
def bv1ToBool (e : bv 1) : bit := expression.bit_test e (expression.bv_nat 1 0)
def boolToBv1 (e : expression bit) : expression (bv 1) := 
  mux e (expression.bv_nat _ 1) (expression.bv_nat _ 0)

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


-- This is substantially different than the handwritten semantics, as we have untyped pointers.
@[reducible]
def Mem : Type := addr (bv 64)

def evaluateAddress (m : Mem) : semantics (expression (bv 64)) := eval (expression.of_addr m)
 
-- x is an immediate usually
-- assume that the int is n bits, extend to m bits.  The K here might be a bit broken?
def handleImmediateWithSignExtend (x : expression int) (n m : Nat) := prim.bv_int_sext m x

-- @[elabSimple]
def extractMInt {w:Nat} (x: expression (bv w)) (u:Nat) (l:Nat)
  : expression (bv ((w - u - 1) + 1 - (w - l))) := slice x (w - u - 1) (w - l)

-- @[elabSimple]
def extract {w:Nat} (x: expression (bv w)) (u:Nat) (l:Nat)
  : expression (bv ((w - u - 1) + 1 - (w - l))) := slice x (w - u - 1) (w - l)

-- notation `pattern` body `pat_end` := mk_pattern body

-- FP compat 
-- def Float2Half (v : expression (float fp32)) (rounding : expression (bv 8)) : expression (float fp16) := 
--   let mk := λ(rm : RoundingMode) => prim.fp_convert_to_fp _ _ rm v;
--   let rc := 
  
-- Int2Float
-- From https://www.felixcloutier.com/x86/cmppd
--                              Comparison operation                            A > B   A < B   A = B   Unordered | Signals on QNaN 
-- EQ_OQ (EQ)	        0H	Equal (ordered, non-signaling)                  False	False	True	False	No
-- LT_OS (LT)	        1H	Less-than (ordered, signaling)                  False	True	False	False	Yes
-- LE_OS (LE)	        2H	Less-than-or-equal (ordered, signaling)         False	True	True	False	Yes
-- UNORD_Q (UNORD)	3H	Unordered (non-signaling)                       False	False	False	True	No

-- NEQ_UQ (NEQ)         4H	Not-equal (unordered, non-signaling)	        True	True	False	True	No
-- NLT_US (NLT)         5H	Not-less-than (unordered, signaling)	        True	False	True	True	Yes
-- NLE_US (NLE)         6H	Not-less-than-or-equal (unordered, signaling)	True	False	False	True	Yes
-- ORD_Q (ORD)          7H	Ordered (non-signaling)	                        True	True	True	False	No

-- EQ_UQ                8H	Equal (unordered, non-signaling)	        False	False	True	True	No
-- NGE_US (NGE)         9H	Not-greater-than-or-equal (unordered, signaling)False	True	False	True	Yes
-- NGT_US (NGT)         AH	Not-greater-than (unordered, signaling)         False	True	True	True	Yes
-- FALSE_OQ(FALSE)	BH	False (ordered, non-signaling)                  False	False	False	False	No

-- NEQ_OQ               CH	Not-equal (ordered, non-signaling)              True	True	False	False	No
-- GE_OS (GE)           DH	Greater-than-or-equal (ordered, signaling)	True	False	True	False	Yes
-- GT_OS (GT)           EH	Greater-than (ordered, signaling)	        True	False	False	False	Yes
-- TRUE_UQ(TRUE)	FH	True (unordered, non-signaling)                 True	True	True	True	No

-- EQ_OS                10H	Equal (ordered, signaling)                      False	False	True	False	Yes
-- LT_OQ                11H	Less-than (ordered, nonsignaling)	        False	True	False	False	No
-- LE_OQ                12H	Less-than-or-equal (ordered, nonsignaling)	False	True	True	False	No
-- UNORD_S              13H	Unordered (signaling)	                        False	False	False	True	Yes
-- NEQ_US               14H	Not-equal (unordered, signaling)	        True	True	False	True	Yes
-- NLT_UQ               15H	Not-less-than (unordered, nonsignaling)	        True	False	True	True	No
-- NLE_UQ               16H	Not-less-than-or-equal (unordered, nonsignaling)True	False	False	True	No
-- ORD_S                17H	Ordered (signaling)	                        True	True	True	False	Yes
-- EQ_US                18H	Equal (unordered, signaling)	                False	False	True	True	Yes
-- NGE_UQ               19H	Not-greater-than-or-equal (unordered, non-s)	False	True	False	True	No
-- NGT_UQ               1AH	Not-greater-than (unordered, nonsignaling)	False	True	True	True	No
-- FALSE_OS             1BH	False (ordered, signaling)	                False	False	False	False	Yes
-- NEQ_OS               1CH	Not-equal (ordered, signaling)	                True	True	False	False	Yes
-- GE_OQ                1DH	Greater-than-or-equal (ordered, nonsignaling)	True	False	True	False	No
-- GT_OQ                1EH	Greater-than (ordered, nonsignaling)	        True	False	False	False	No
-- TRUE_US              1FH	True (unordered, signaling)	                True	True	True	True	Yes

-- The bits are (from MSB):S U N FF
-- where
-- - FF are the operation bits 
-- - N if negated
-- - U interprets unordered
-- - S interprets signaling (currently ignored)

def cmp_pred_tbl {fc : float_class} : List (Nat × (expression (float fc) -> expression (float fc) -> expression bit) × Bool) := 
    [ (0, eq,    false) 
    , (1, @fp_lt fc, false)
    , (2, @fp_le fc, false)
    , (3, λ_ _ => bit_zero, true)
    ]

def cmp_pred (fc : float_class) (op : expression (bv 8)) (v1 v2 : expression (float fc))  : expression bit :=
  -- entries: index, function if ordered, result if unordered

  let cmp_pred_tbl : List (Nat × (expression (float fc) -> expression (float fc) -> expression bit) × Bool) := 
    [ (0, eq,    false) 
    , (1, @fp_lt fc, false)
    , (2, @fp_le fc, false)
    , (3, λ_ _ => bit_zero, true)
    ];

  let u_bit := expression.bit_test op (expression.bv_nat 8 3);
  let n_bit := expression.bit_test op (expression.bv_nat 8 2);
  let op_bits := slice op 1 0;
  let mk : (expression (float fc) -> expression (float fc) -> expression bit) × Bool -> expression bit
     := λ(f, ordered) => 
    neq n_bit (mux (prim.fp_ordered _ v1 v2) (f v1 v2) (if ordered then notBool_ u_bit else u_bit));
  let mk2 : (Nat × (expression (float fc) -> expression (float fc) -> expression bit) × Bool)
           -> expression bit -> expression bit 
          := λ(ix, f) => mux (eq op_bits (expression.bv_nat _ ix)) (mk f);
  List.foldr mk2 bit_zero cmp_pred_tbl

def fp_lift (fc : float_class) {tp : type} (f : expression (float fc) -> expression (float fc) -> expression tp)
            (x y : expression (bv fc.width)) : expression tp :=
    f (bv_bitcast_to_fp _ x) (bv_bitcast_to_fp _ y)

def cmp_double_pred (v1 v2 : expression (bv 64)) (op : expression (bv 8)) : expression (bv 1) :=
  boolToBv1 (fp_lift _ (cmp_pred fp64 op) v1 v2)

def cmp_single_pred (v1 v2 : expression (bv 32)) (op : expression (bv 8)) : expression (bv 1) :=
  boolToBv1 (fp_lift _ (cmp_pred fp32 op) v1 v2)

-- -- -- comisd
-- -- -- comiss

-- These operations work on the underlying bit representation (i.e., they need to bitcast to/from FP)
def cvt_double_to_int32_truncate (v : expression (bv 64)) : expression (bv 32) := 
  prim.fp_convert_to_int fp64 _ RoundingMode.Truncate (bv_bitcast_to_fp _ v)
def cvt_double_to_int64_truncate (v : expression (bv 64)) : expression (bv 64) :=
  prim.fp_convert_to_int fp64 _ RoundingMode.Truncate (bv_bitcast_to_fp _ v)
def cvt_single_to_int32_truncate (v : expression (bv 32)) : expression (bv 32) :=
  prim.fp_convert_to_int fp32 _ RoundingMode.Truncate (bv_bitcast_to_fp _ v)
def cvt_single_to_int64_truncate (v : expression (bv 32)) : expression (bv 64) :=
  prim.fp_convert_to_int fp32 _ RoundingMode.Truncate (bv_bitcast_to_fp _ v)

-- P RS RC 
-- P  - 1 bit precision 0: normal, 1: inexact
-- RS - 1 bit rounding select 1: MXCSR.RC 0: imm8
-- RC - 2 bit rounding mode

def cvt_to_int_rm (fc : float_class) (v : expression (bv fc.width)) (rounding : expression (bv 8)) : expression (bv fc.width) :=
  let cvt_tbl : List (Nat × RoundingMode) :=
    [ (0, RoundingMode.ClosestEven) 
    , (1, RoundingMode.RoundDown)
    , (2, RoundingMode.RoundUp)
    , (3, RoundingMode.Truncate)
    ];
  -- let p  := expression.bit_test rounding (expression.bv_nat 8 3);
  -- let rs := expression.bit_test rounding (expression.bv_nat 8 2);
  let rc := slice rounding 1 0;
  let mk rm := fp_bitcast_to_bv 
                 (prim.int_convert_to_fp _ _
                    (prim.fp_convert_to_int fc fc.width rm (bv_bitcast_to_fp _ v))) 
                 fc.width;
  let mk2 : (Nat × RoundingMode) -> expression (bv fc.width) -> expression (bv fc.width)
     := λ(ix, rm) => mux (eq rc (expression.bv_nat _ ix)) (mk rm);
  List.foldr mk2 (mk RoundingMode.Truncate) cvt_tbl

def cvt_double_to_int64_rm (v : expression (bv 64)) (rounding : expression (bv 8)) : expression (bv 64) :=
  cvt_to_int_rm fp64 v rounding

def cvt_single_to_int32_rm (v : expression (bv 32)) (rounding : expression (bv 8)) : expression (bv 32) :=
  cvt_to_int_rm fp32 v rounding

-- FIXME: rounding mode should come from the MXCSR
def fp_round {fc : float_class} (dest_fc : float_class) (v : expression (float fc)) : expression (float dest_fc) :=
  prim.fp_convert_to_fp fc dest_fc RoundingMode.ClosestEven v


-- FIXME: we could use mux and fp_lt here, but there are side
-- conditions if e.g. they are both zero (and the usual NaN issues)
-- returns 1 if the first is > than the second
def maxcmp_double (x y : expression (bv 64)) : expression (bv 1) :=
  boolToBv1 (fp_lift fp64 (fun a b => prim.fp_max _ a b) x y)

def maxcmp_single (x y : expression (bv 32)) : expression (bv 1) :=
  boolToBv1 (fp_lift fp32 (fun a b => prim.fp_max _ a b) x y)

def mincmp_double (x y : expression (bv 64)) : expression (bv 1) :=
  boolToBv1 (fp_lift fp64 (fun a b => prim.fp_min _ a b) x y)

def mincmp_single  (x y : expression (bv 32)) : expression (bv 1) :=
  boolToBv1 (fp_lift fp32 (fun a b => prim.fp_min _ a b) x y)

def sqrt_double (x : expression (bv 64)) : expression (bv 64) :=
  fp_bitcast_to_bv (prim.fp_sqrt fp64 (bv_bitcast_to_fp _ x)) 64

def sqrt_single (x : expression (bv 32)) : expression (bv 32) :=
  fp_bitcast_to_bv (prim.fp_sqrt fp32 (bv_bitcast_to_fp _ x)) 32

instance {fc: float_class} : OfScientific (expression (float fc)) where
  ofScientific m s e := prim.fp_literal fc m s e

-- uvalueMInt
-- vfmadd132_double
-- vfnmadd132_double
-- vfnmadd132_single
-- vfnmadd213_double
-- vfnmadd213_single
-- vfnmadd231_double

end k_x86_semantics
end x86
