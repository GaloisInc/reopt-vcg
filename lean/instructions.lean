import .common
import system.io

namespace x86

------------------------------------------------------------------------
-- Notation

open mc_semantics
open mc_semantics.type
open reg
open semantics

notation `pattern` body `pat_end` := mk_pattern body

-- Introduces notation x[h..l] to slice the h..l bits out of x.
local notation x `[[`:1025 h `..` l `]]` := slice x h l

local infix ≠ := neq

local infix = := eq

local notation `⇑`:max x:max := coe1 x

local notation ℕ := nat_expr

infix `.=`:20 := set

notation d `.=` a `|` s :20 := set_aligned d s a

------------------------------------------------------------------------
-- bitvector functions

-- `off` is the index of the bit to return.
-- TODO: figure out how to handle out of bounds and any other edge cases and document the
-- assumptions.
def bv_bit {w:ℕ} (base : bv w) (off : bv w) : bit := prim.bvbit w base off -- Note that if `off` exceeds w, bvBit v off should return `zero`
def bv_xor {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bvxor w x y
def bv_shl {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.shl w x y
def bv_shr {w:ℕ} (x y : bv w) : bv w := prim.shr w x y
def bv_sar {w:ℕ} (x y : bv w) : bv w := prim.sar w x y
def bv_complement {w:ℕ} (b : bv w) : bv w := prim.complement w b
def bv_is_zero {w:ℕ} (b : bv w) : bit := b = 0
def bv_and {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bvand w x y
def bv_or {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bvor w x y
def bv_cat {w:ℕ} (x : bv w) (y : bv w) : bv (2*w) := prim.bvcat w x y
def bv_least_nibble {w:ℕ} (x : bv w) : bv 4 := prim.bv_least_nibble w x
def bv_ule {w:ℕ} (x y : bv w) : bit := prim.bv_ule w x y
def bv_ult {w:ℕ} (x y : bv w) : bit := prim.bv_ult w x y
def bv_sub {w:ℕ} (x y : bv w) : bv w := prim.bvsub w x y

def msb {w:ℕ} (v : bv w) : bit := prim.msb w v
def least_byte {w:ℕ} (v : bv w) : bv 8 := prim.least_byte w v
def even_parity {w:ℕ} (v : bv w) : bit := prim.even_parity w v

infixl `.|.`:65 := bv_or
infixl `.&.`:70 := bv_and

------------------------------------------------------------------------
-- utility functions

def nat_to_bv {w:ℕ} (n:ℕ) : bv w := prim.bvnat w n

def set_undefined {tp:type} (v : lhs tp) : semantics unit := do
  semantics.add_action (action.set_undef v)

def set_undefined_cond {tp:type} (v : lhs tp) (cond: expression bit) : semantics unit := do
  semantics.add_action (action.set_undef_cond v cond)

def set_overflow (b:bit) : semantics unit := do
  cf .= b,
  of .= b,
  set_undefined sf,
  set_undefined zf,
  set_undefined af,
  set_undefined pf

def set_result_flags {w:ℕ} (res : bv w) : semantics unit := do
  sf .= msb res,
  zf .= bv_is_zero res,
  pf .= even_parity (least_byte res)

def set_bitwise_flags {w:ℕ} (res : bv w) : semantics unit := do
  of .= zero,
  cf .= zero,
  set_undefined af,
  set_result_flags res

def ssbb_overflows  {w:ℕ} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.ssbb_overflows w dest src borrow
def ssub_overflows  {w:ℕ} (dest : bv w) (src : bv w)                : bit := ssbb_overflows dest src zero

def usbb_overflows  {w:ℕ} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.usbb_overflows w dest src borrow
def usub_overflows  {w:ℕ} (dest : bv w) (src : bv w)                : bit := usbb_overflows dest src zero
def usub4_overflows {w:ℕ} (dest : bv w) (src : bv w)                : bit := usub_overflows (bv_least_nibble dest) (bv_least_nibble src)

def uadc_overflows  {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.uadc_overflows w dest src carry
def uadc4_overflows {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := uadc_overflows (bv_least_nibble dest) (bv_least_nibble src) carry
def uadd_overflows  {w:ℕ} (dest : bv w) (src : bv w)               : bit := uadc_overflows dest src zero
def uadd4_overflows {w:ℕ} (dest : bv w) (src : bv w)               : bit := uadd_overflows (bv_least_nibble dest) (bv_least_nibble src)

def sadc_overflows  {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.sadc_overflows w dest src carry
def sadd_overflows  {w:ℕ} (dest : bv w) (src : bv w)               : bit := sadc_overflows dest src zero

def do_cmp {w:ℕ} (x : bv w) (y : bv w) : semantics unit := do
  of .= ssub_overflows x y,
  af .= usub4_overflows x y,
  cf .= usub_overflows x y,
  set_result_flags (x - y)

def push {w: one_of [8, 16, 32, 64]} (value : bv w) : semantics unit := do
  rsp .= ⇑rsp - (nat_to_bv (one_of.to_nat_expr w)),
  ⇑rsp .= uext value 64,
  return ()

def pop (w: ℕ) (additional : bv 16) : semantics (bv w) := do
  temp ← eval ⇑rsp,
  let count := nat_to_bv w + uext additional 64 in do
  rsp .= ⇑rsp + count,
  return (uext temp w)

def do_xchg {w:ℕ} (addr1 : bv w) (addr2 : bv w) : semantics unit :=
  record_event (event.xchg addr1 addr2)

-- Generic shift operation, takes functions for doing the shift and
-- setting the flags.
def do_sh {w:ℕ}
          (count: bv 8)                  -- amount to shift by
          (count_mask: bv 8)             -- mask for the counter
          (v: lhs (bv w))                -- value to be shifted
          (shift: bv w → bv w → bv w)    -- shift operation
          (cf_update: bv w → bv 8 → bit) -- update function for carry flag
          (of_update: bv w → bv w → bit) -- update function for overflow flag
          : semantics unit := do
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  let low_count := count .&. count_mask,
  -- compute the result
  let res := shift v (uext low_count w),
  -- When the count is zero, nothing happens, and no flags change
  let is_nonzero := low_count ≠ 0,
  -- Set the af flag
  set_undefined_cond af is_nonzero,
  let cf_bit := cf_update res low_count,
  set_cond cf is_nonzero cf_bit,
  let of_bit := of_update v res,
  -- We set `of` twice, to keep the logic a bit simpler: `of` should
  -- only be set by the result when low_count = 1, and in other cases
  -- it should either be unaffected or undefined (low_count = 0
  -- vs. low_count > 1).
  set_undefined_cond of (expression.or is_nonzero (low_count ≠ 1)),
  set_cond of (low_count = 1) of_bit,
  set_cond sf is_nonzero (msb res),
  set_cond zf is_nonzero (res = 0),
  set_cond pf is_nonzero (even_parity (least_byte res)),
  set_cond v  is_nonzero res

------------------------------------------------------------------------
-- imul definition

def imul : instruction :=
 definst "imul" $ do
   pattern λ(src : bv 8), do
     tmp ← eval $ sext (⇑al) 16 * sext src _,
     ax .= tmp,
     set_overflow $ sext tmp[[7..0]] _ ≠ tmp
   pat_end,
   pattern λ(src : bv 16), do
     tmp ← eval $ sext (⇑ax) 32 * sext src _,
     dx .= tmp[[31..16]],
     ax .= tmp[[15.. 0]],
     set_overflow $ sext tmp[[15..0]] _ ≠ tmp
   pat_end,
   pattern λ(src : bv 32), do
     tmp ← eval $ sext ⇑eax 64 * sext src _,
     edx .= tmp[[63..32]],
     eax .= tmp[[31.. 0]],
     set_overflow $ sext tmp[[31..0]] _ ≠ tmp
   pat_end,
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : bv w), do
     tmp     ← eval $ sext ⇑dest (2*w) * sext src (2*w),
     tmp_low ← eval $ trunc tmp w,
     dest .= tmp_low,
     set_overflow $ sext tmp_low (2*w) ≠ tmp
   pat_end,
   pattern λ(w : one_of [16,32,64]) (dest : lhs (bv w)) (src1 src2 : bv w), do
     tmp     ← eval $ sext ⇑src1 (2*w) * sext src2 (2*w),
     tmp_low ← eval $ trunc tmp w,
     dest .= tmp_low,
     set_overflow $ sext tmp_low (2*w) ≠ tmp
   pat_end

------------------------------------------------------------------------
-- mul definition

def mul : instruction := do
 definst "mul" $ do
   pattern λ(src : bv 8), do
     tmp ← eval $ uext ⇑al 16 * uext src 16,
     ax .= tmp,
     set_overflow $ tmp[[16..8]] ≠ 0
   pat_end,
   pattern λ(src : bv 16), do
     tmp ← eval $ uext (⇑ax) 32 * uext src _,
     dx .= tmp[[31..16]],
     ax .= tmp[[15.. 0]],
     set_overflow $ tmp[[31..16]] ≠ 0
   pat_end,
   pattern λ(src : bv 32), do
     tmp ← eval $ uext ⇑eax 64 * uext src _,
     edx .= tmp[[63..32]],
     eax .= tmp[[31.. 0]],
     set_overflow $ tmp[[63..32]] ≠ 0
   pat_end,
   pattern λ(src : bv 64), do
     tmp ← eval $ uext ⇑rax 128 * uext src _,
     rdx .= tmp[[127..64]],
     rax .= tmp[[63 .. 0]],
     set_overflow $ tmp[[127..64]] ≠ 0
   pat_end

------------------------------------------------------------------------
-- mov definition

def mov : instruction := do
 definst "mov" $ do
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : bv w), do
     dest .= src
   pat_end

------------------------------------------------------------------------
-- mov definition
-- Move Data from String to String

-- def movs : instruction := do
--  definst "movs" $ do sorry

------------------------------------------------------------------------
-- movsx definition
-- Move with Sign-Extension

def movsx : instruction := do
 definst "movsx" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [8, 16]) (dest : lhs (bv w)) (src : bv u), do
     dest .= sext src w
   pat_end

------------------------------------------------------------------------
-- movsxd definition
-- Move with Sign-Extension

def movsxd : instruction := do
 definst "movsxd" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [16, 32]) (dest : lhs (bv w)) (src : bv u), do
     dest .= sext src w
   pat_end

------------------------------------------------------------------------
-- movzx definition
-- Move with Zero-Extend

def movzx : instruction := do
 definst "movzx" $ do
   pattern λ(w : one_of [16,32,64]) (u : one_of [8, 16]) (dest : lhs (bv w)) (src : bv u), do
     dest .= uext src w
   pat_end

------------------------------------------------------------------------
-- movdqa definition
-- Move Aligned Packed Integer Values

def movdqa : instruction := do
 definst "movdqa" $ do
   pattern λ(n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : vec n (bv 32)), do
     dest .= 16 | src
   pat_end

------------------------------------------------------------------------
-- movaps definition
-- Move Aligned Packed Single-Precision Floating-Point Values

def movaps : instruction := do
 definst "movaps" $ do
   pattern λ(n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : vec n (bv 32)), do
     dest .= 16 | src
   pat_end

------------------------------------------------------------------------
-- xchg definition
-- Exchange Register/Memory with Register
def xchg : instruction := do
 definst "xchg" $ do
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : lhs (bv w)), do
     do_xchg ⇑dest ⇑src
   pat_end

------------------------------------------------------------------------
-- cmps definition
-- Compare String Operands

-- def cmps : instruction := do
--  definst "cmps" $ sorry
   --pattern λ(w : one_of [8,16,32,64]) (dest : bv w) (src : bv w)
   --pat_end

------------------------------------------------------------------------
-- cmp definition
-- Compare Two Operands

def cmp : instruction := do
 definst "cmp" $ do
   pattern λ(u v : one_of [8,16,32,64]) (src1 : bv u) (src2 : bv v), do
     do_cmp src1 (sext src2 u)
   pat_end

------------------------------------------------------------------------
-- cmpxchg definition
-- Compare and Exchange

/-

This instruction should be fairly straigth forward in the register-only
case, but requires more care for the memory case. We will probably also
need a notion of muxing on a bit.

def cmpxchg : instruction := do
 definst "cmpxchg" $ do
   pattern λ(dest : lhs (bv 8)) (src : bv 8), do
     temp ← eval $ ⇑dest,
     do_cmp ⇑al temp,
     zf .= temp = dest
   pat_end
-/

------------------------------------------------------------------------
-- dec definition
-- Decrement by 1

def dec : instruction := do
 definst "dec" $ do
   pattern λ(w : one_of [8,16,32,64]) (value : lhs (bv w)), do
     temp ← eval $ ⇑value - 1,
     of .= ssub_overflows temp 1,
     af .= usub4_overflows temp 1,
     set_result_flags temp,
     value .= temp
   pat_end

------------------------------------------------------------------------
-- inc definition
-- Increment by 1

def inc : instruction := do
 definst "inc" $ do
   pattern λ(w : one_of [8,16,32,64]) (value : lhs (bv w)), do
     temp ← eval $ ⇑value + 1,
     of .= sadd_overflows temp 1,
     af .= uadd4_overflows temp 1,
     set_result_flags temp,
     value .= temp
   pat_end

------------------------------------------------------------------------
-- neg definition
-- Two's Complement Negation

def neg : instruction := do
 definst "neg" $ do
   pattern λ(w : one_of [8,16,32,64]) (dest : lhs (bv w)), do
     cf .= bv_is_zero ⇑dest,
     of .= ssub_overflows 0 ⇑dest,
     af .= usub4_overflows 0 ⇑dest,
     r ← eval $ -⇑dest,
     set_result_flags r,
     dest .= r
   pat_end

------------------------------------------------------------------------
-- nop definition
-- No Operation

def nop : instruction := do
 definst "nop" $ do
   pattern do
     (return () : semantics unit)
   pat_end,
   pattern λ(w : one_of [16, 32]), do
     (return () : semantics unit)
   pat_end

------------------------------------------------------------------------
-- pause definition
-- Spin Loop Hint

def pause : instruction := do
 definst "pause" $ do
   pattern do
     (return () : semantics unit)
   pat_end

------------------------------------------------------------------------
-- div definition
-- Unsigned Divide

def div : instruction := do
 definst "div" $ do
   -- TODO: would it be better to have a single div primitive?
   pattern λ(src : bv 8), do
     tempQuot ← eval $ expression.quot ⇑ax (uext src 16),
     tempRem  ← eval $ expression.rem  ⇑ax (uext src 16),
     al .= tempQuot[[7..0]],
     ah .= tempRem[[7..0]]
   pat_end,
   pattern λ(src : bv 16), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑dx ⇑ax) (uext src 32),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑dx ⇑ax) (uext src 32),
     ax .= tempQuot[[15..0]],
     dx .= tempRem[[15..0]]
   pat_end,
   pattern λ(src : bv 32), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑edx ⇑eax) (uext src 64),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑edx ⇑eax) (uext src 64),
     eax .= tempQuot[[31..0]],
     edx .= tempRem[[31..0]]
   pat_end,
   pattern λ(src : bv 64), do
     tempQuot ← eval $ expression.quot (bv_cat ⇑rdx ⇑rax) (uext src 128),
     tempRem  ← eval $ expression.rem  (bv_cat ⇑rdx ⇑rax) (uext src 128),
     rax .= tempQuot[[63..0]],
     rdx .= tempRem[[63..0]]
   pat_end

------------------------------------------------------------------------
-- idiv definition
-- Signed Divide

def idiv : instruction := do
 definst "idiv" $ do
   -- TODO: would it be better to have a single div primitive?
   pattern λ(src : bv 8), do
     tempQuot ← eval $ expression.signed_quot ⇑ax (uext src 16),
     tempRem  ← eval $ expression.signed_rem  ⇑ax (uext src 16),
     al .= tempQuot[[7..0]],
     ah .= tempRem[[7..0]]
   pat_end,
   pattern λ(src : bv 16), do
     tempQuot ← eval $ expression.signed_quot (bv_cat ⇑dx ⇑ax) (uext src 32),
     tempRem  ← eval $ expression.signed_rem  (bv_cat ⇑dx ⇑ax) (uext src 32),
     ax .= tempQuot[[15..0]],
     dx .= tempRem[[15..0]]
   pat_end,
   pattern λ(src : bv 32), do
     tempQuot ← eval $ expression.signed_quot (bv_cat ⇑edx ⇑eax) (uext src 64),
     tempRem  ← eval $ expression.signed_rem  (bv_cat ⇑edx ⇑eax) (uext src 64),
     eax .= tempQuot[[31..0]],
     edx .= tempRem[[31..0]]
   pat_end,
   pattern λ(src : bv 64), do
     tempQuot ← eval $ expression.signed_quot (bv_cat ⇑rdx ⇑rax) (uext src 128),
     tempRem  ← eval $ expression.signed_rem  (bv_cat ⇑rdx ⇑rax) (uext src 128),
     rax .= tempQuot[[63..0]],
     rdx .= tempRem[[63..0]]
   pat_end

------------------------------------------------------------------------
-- and definition
-- Logical AND

def and : instruction := do
 definst "and" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ ⇑dest .&. src,
     set_bitwise_flags tmp,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- not definition
-- One's Complement Negation

def not : instruction := do
 definst "not" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)), do
     dest .= bv_complement ⇑dest
   pat_end

------------------------------------------------------------------------
-- or definition
-- Logical Inclusive OR

def or : instruction := do
 definst "or" $ do
   pattern λ(u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : bv v), do
     dest .= ⇑dest .|. sext src u,
     set_undefined af,
     of .= zero,
     cf .= zero,
     set_result_flags ⇑dest
   pat_end

------------------------------------------------------------------------
-- xor definition
-- Logical Exclusive OR

def xor : instruction := do
 definst "xor" $ do
   pattern λ(u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : bv v), do
     dest .= bv_xor ⇑dest (sext src u),
     set_undefined af,
     of .= zero,
     cf .= zero,
     set_result_flags ⇑dest
   pat_end

------------------------------------------------------------------------
-- test definition
-- Logical compare
def test : instruction :=
 definst "test" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (x y : bv w), do
     set_bitwise_flags (x .&. y)
   pat_end

------------------------------------------------------------------------
-- bt definition
-- Bit Test

def bt : instruction := do
 definst "bt" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : bv w) (off : bv w), do
     cf .= bv_bit ⇑base off
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : bv w) (off : bv 8), do
     cf .= bv_bit ⇑base (uext off w)
   pat_end

------------------------------------------------------------------------
-- btc definition
-- Bit Test and Complement

def btc : instruction := do
 definst "btc" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= bv_xor ⇑base (bv_shl 1 off)
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= bv_xor ⇑base (uext (bv_shl 1 off) w)
   pat_end

------------------------------------------------------------------------
-- btr definition
-- Bit Test and Reset

def btr : instruction := do
 definst "btr" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= ⇑base .&. (bv_complement (bv_shl 1 off))
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= ⇑base .&. (bv_complement (uext (bv_shl 1 off) w))
   pat_end

------------------------------------------------------------------------
-- bts definition
-- Bit Test and Set

def bts : instruction := do
 definst "bts" $ do
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv w), do
     cf   .= bv_bit ⇑base off,
     base .= ⇑base .|. (bv_shl 1 off)
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : lhs (bv w)) (off : bv 8), do
     cf   .= bv_bit ⇑base (uext off w),
     base .= ⇑base .|. (uext (bv_shl 1 off) w)
   pat_end

------------------------------------------------------------------------
-- bsf definition
-- Bit Scan Forward

def bsf_def : instruction := do
 definst "bsf" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     set_undefined cf,
     set_undefined of,
     set_undefined sf,
     set_undefined af,
     set_undefined pf,
     zf .= bv_is_zero y,
     r .= bsf y
  pat_end

------------------------------------------------------------------------
-- bsr definition
-- Bit Scan Reverse

def bsr_def : instruction := do
 definst "bsr" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     set_undefined cf,
     set_undefined of,
     set_undefined sf,
     set_undefined af,
     set_undefined pf,
     zf .= bv_is_zero y,
     r .= bsr y
  pat_end

------------------------------------------------------------------------
-- bswap definition
-- Byte Swap

def bswap : instruction := do
 definst "bswap" $ do
   pattern λ(w : one_of [32, 64]) (dest : lhs (bv w)), do
     dest .= expression.bswap ⇑dest
   pat_end

------------------------------------------------------------------------
-- add definition

def add : instruction := do
 definst "add" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ ⇑dest + src,
     set_result_flags tmp,
     cf .= uadd_overflows tmp src,
     of .= sadd_overflows tmp src,
     af .= uadd4_overflows tmp src,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- adc definition
-- Add with Carry

def adc : instruction := do
 definst "adc" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ expression.adc ⇑dest src cf,
     set_result_flags tmp,
     cf .= uadc_overflows  tmp src cf,
     of .= sadc_overflows  tmp src cf,
     af .= uadc4_overflows tmp src cf,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- xadd definition
-- Exchange and Add

def xadd : instruction := do
 definst "xadd" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : lhs (bv w)), do
     tmp ← eval $ ⇑dest + ⇑src,
     src .= ⇑dest,
     set_result_flags tmp,
     cf .= uadd_overflows  tmp src,
     of .= sadd_overflows  tmp src,
     af .= uadd4_overflows tmp src,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- fadd definition

def fadd : instruction := do
 definst "fadd" $ do
   pattern λ(dest : lhs x86_80) (src : lhs x86_80), do
     dest .= x87_fadd dest src
   pat_end,
   pattern λ(src : lhs float), do
     st0  .= x87_fadd st0 ↑src
   pat_end,
   pattern λ(src : lhs double), do
     st0  .= x87_fadd st0 ↑src
   pat_end

------------------------------------------------------------------------
-- faddp definition

def faddp : instruction := do
 definst "faddp" $ do
   pattern λ(dest : lhs x86_80) (src : lhs x86_80), do
     dest .= x87_fadd dest src,
     record_event event.pop_x87_register_stack
   pat_end

------------------------------------------------------------------------
-- fiadd definition

def fiadd : instruction := do
 definst "fiadd" $ do
   pattern λ(w : one_of [16,32]) (src : lhs (bv w)), do
     st0 .= x87_fadd st0 ↑src
   pat_end

------------------------------------------------------------------------
-- syscall definition

def syscall : instruction :=
  definst "syscall" $ mk_pattern (record_event event.syscall)

------------------------------------------------------------------------
-- hlt definition
-- Halt

def hlt : instruction :=
  definst "hlt" $ mk_pattern (record_event event.hlt)

------------------------------------------------------------------------
-- sub definition

def sub : instruction := do
 definst "sub" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : bv w), do
     tmp ← eval $ ⇑dest - src,
     set_result_flags tmp,
     cf .= usub_overflows tmp src,
     of .= ssub_overflows tmp src,
     af .= usub4_overflows tmp src,
     dest .= tmp
   pat_end

------------------------------------------------------------------------
-- lea definition
-- Load Effective Address

def lea : instruction :=
 definst "lea" $ do
   pattern λ(w : one_of [16, 32, 64]) (dest : lhs (bv w)) (src : bv 64), do
     dest .= trunc src w
   pat_end

------------------------------------------------------------------------
-- call definition
-- Call Procedure

def call : instruction :=
 definst "call" $ do
   pattern λ(w : one_of [16, 32, 64]) (v : bv w), do
     record_event (event.call (uext v 64))
   pat_end

------------------------------------------------------------------------
-- jmp definition
-- Jump
def jmp : instruction :=
 definst "jmp" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (v : bv w), do
     record_event (event.jmp (uext v 64))
   pat_end

------------------------------------------------------------------------
-- Jcc definition
-- Conditional jumps

def mk_jcc_instruction : string × expression bit → instruction
 | (name, cc) := definst name $ do
 pattern λ(w : one_of [8, 16, 32, 64]) (addr : bv w), do
   record_event (event.branch cc (uext addr 64))
 pat_end

def mk_jcc_instruction_aliases : list string × expression bit → list instruction
 | (names, cc) := list.map (λn, mk_jcc_instruction (n, cc)) names

-- Conditional jump instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.
def jcc_instructions : list instruction := list.join $ list.map mk_jcc_instruction_aliases
 [ -- Jump if above (cf = 0 and zf = 0)
   (["ja", "jnbe"], expression.and (expression.get cf = zero) (expression.get zf = zero))
   -- Jump if above or equal (cf = 0)
 , (["jae", "jnb", "jnc"], expression.get cf = zero)
   -- Jump if below (cf = 1)
 , (["jb", "jc", "jnae"], expression.get cf = one)
   -- Jump if below or equal (cf = 1 or zf = 1)
 , (["jbe"], expression.or (expression.get cf = one) (expression.get zf = one))
   -- Jump if CX is 0
 , (["jcxz"], expression.get cx = 0)
   -- Jump if ECX is 0
 , (["jecxz"], expression.get ecx = 0)
   -- Jump if RCX is 0
 , (["jrcxz"], expression.get rcx = 0)
   -- Jump if equal (zf = 1)
 , (["je", "jz"], expression.get zf = one)
   -- Jump if greater (zf = 0 and sf = of)
 , (["jg", "jnle"], expression.and (expression.get zf = zero) (expression.get sf = expression.get of))
   -- Jump if greater or equal (sf = of)
 , (["jge", "jnl"], expression.get sf = expression.get of)
   -- Jump if less (sf ≠ of)
 , (["jl", "jnge"], expression.get sf ≠ expression.get of)
   -- Jump if less or equal (zf = 1 or sf ≠ of)
 , (["jle", "jng"], expression.or (expression.get zf = one) (expression.get sf ≠ expression.get of))
   -- Jump if not above (cf = 1 or zf = 1)
 , (["jna"], expression.or (expression.get cf = one) (expression.get zf = one))
   -- Jump if not equal (zf = 0)
 , (["jne", "jnz"], expression.get zf = zero)
   -- Jump if not overflow (of = 0)
 , (["jno"], expression.get of = zero)
   -- Jump if not parity (pf = 0)
 , (["jnp", "jpo"], expression.get pf = zero)
   -- Jump if not sign (sf = 0)
 , (["jns"], expression.get sf = zero)
   -- Jump if overflow (of = 1)
 , (["jo"], expression.get of = one)
   -- Jump if parity (pf = 1)
 , (["jp", "jpe"], expression.get pf = one)
   -- Jump if sign (sf = 1)
 , (["js"], expression.get sf = one)
 ]

------------------------------------------------------------------------
-- ret definition
-- Return from Procedure
def ret : instruction :=
 definst "ret" $ do
   pattern do
     pop 64 0,
     -- pop 64,
     record_event event.ret
   pat_end,
   pattern λ(off : bv 16), do
     pop 64 off,
     record_event event.ret
   pat_end

------------------------------------------------------------------------
-- leave definition
-- High Level Procedure Exit
def leave : instruction :=
 definst "leave" $ do
   pattern do
     rsp .= ⇑rbp,
     v ← pop 64 0,
     rbp .= v
   pat_end

------------------------------------------------------------------------
-- pop definition
-- Pop a Value from the Stack
def pop_def : instruction :=
 definst "pop" $ do
   pattern λ(w : one_of [16, 32, 64]) (dest: lhs (bv w)),do
     v ← pop (one_of.to_nat_expr w) 0,
     dest .= v
   pat_end

------------------------------------------------------------------------
-- push definition
-- Push Word, Doubleword or Quadword Onto the Stack
def push_def : instruction :=
 definst "push" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (value: bv w),do
     push value
   pat_end

------------------------------------------------------------------------
-- cwd definition
-- Convert Word to Doubleword
def cwd : instruction :=
 definst "cwd" $ do
   pattern do
     let doubleword := sext ⇑ax 32, do
     dx .= doubleword[[31..16]]
   pat_end

------------------------------------------------------------------------
-- cdq definition
-- Convert Doubleword to Quadword
def cdq : instruction :=
 definst "cdq" $ do
   pattern do
     let quadword := sext ⇑eax 64, do
     edx .= quadword[[63..32]]
   pat_end

------------------------------------------------------------------------
-- cqo definition
-- Convert Quadword to Octword
def cqo : instruction :=
 definst "cqo" $ do
   pattern do
     let octword := sext ⇑rax 128, do
     rdx .= octword[[127..64]]
   pat_end

------------------------------------------------------------------------
-- cbw definition
-- Convert Byte to Word
def cbw : instruction :=
 definst "cbw" $ do
   pattern do
     ax .= sext ⇑al 16
   pat_end

------------------------------------------------------------------------
-- cwde definition
-- Convert Word to Doubleword
def cwde : instruction :=
 definst "cwde" $ do
   pattern do
     eax .= sext ⇑ax 32
   pat_end

------------------------------------------------------------------------
-- cdqe definition
-- Convert Doubleword to Quadword
def cdqe : instruction :=
 definst "cdqe" $ do
   pattern do
     rax .= sext ⇑eax 64
   pat_end

------------------------------------------------------------------------
-- clc definition
-- Clear Carry Flag
def clc : instruction :=
 definst "clc" $ do
   pattern do
     cf .= zero
   pat_end

------------------------------------------------------------------------
-- cld definition
-- Clear Direction Flag
def cld : instruction :=
 definst "cld" $ do
   pattern do
     df .= zero
   pat_end

------------------------------------------------------------------------
-- sar definition
-- Shift arithmetic right
def sar : instruction :=
  definst "sar" $ do
    let set_cf {w:ℕ} v i :=
      let notInRange := bv_ult (expression.bvnat 8 w) i in
      let msb_v := bv_bit v (expression.bvnat w (w-1)) in
      expression.or (bv_bit v ((uext i w) - 1))
                    (expression.and notInRange msb_v),
    pattern λ(w : one_of [8, 16, 32]) (value: lhs (bv w)) (count: bv 8),do
      do_sh count (32-1) value bv_sar set_cf (λv res, zero)
    pat_end,
    pattern λ(value: lhs (bv 64)) (count: bv 8),do
      do_sh count (64-1) value bv_sar set_cf (λv res, zero)
    pat_end

------------------------------------------------------------------------
-- shr definition
-- Shift logical right
def shr : instruction :=
  definst "shr" $ do
    let set_cf {w:ℕ} v (i: bv 8) := bv_bit v (bv_sub (uext i w) 1),
    let set_of {w:ℕ} v res := expression.xor (@msb w res) (@msb w v),
    pattern λ(w : one_of [8, 16, 32]) (value: lhs (bv w)) (count: bv 8),do
      do_sh count (32-1) value bv_shr set_cf set_of
    pat_end,
    pattern λ(value: lhs (bv 64)) (count: bv 8),do
      do_sh count (64-1) value bv_shr set_cf set_of
    pat_end

------------------------------------------------------------------------
-- sal & shl definition
-- Shift arithmetic left
def sal_patterns := do
  let set_cf {w:ℕ} v (i : bv 8) :=
        expression.and (bv_ule i (expression.bvnat _ w))
                       (bv_bit v (bv_sub (expression.bvnat _ w) (uext i w))),
  pattern λ(w : one_of [8, 16, 32]) (value: lhs (bv w)) (count: bv 8),do
    do_sh count (32-1) value bv_shl set_cf (λv res, msb v)
  pat_end,
  pattern λ(value: lhs (bv 64)) (count: bv 8), do
    do_sh count (64-1) value bv_shl set_cf (λv res, msb v)
  pat_end

def sal : instruction := definst "sal" sal_patterns
def shl : instruction := definst "shl" sal_patterns

def all_instructions :=
  [ imul
  , mul
  , mov
  , movsx
  , movsxd
  , movzx
  , xchg
  , cmp
  , dec
  , inc
  , neg
  , nop
  , pause
  , div
  , idiv
  , and
  , not
  , or
  , bt
  , btc
  , btr
  , bts
  , bsf_def
  , bsr_def
  , bswap
  , add
  , adc
  , xadd
  , fadd
  , faddp
  , fiadd
  , syscall
  , hlt
  , lea
  , call
  , jmp
  , ret
  , leave
  , pop_def
  , push_def
  , cwd
  , cdq
  , cqo
  , cbw
  , cwde
  , cdqe
  , clc
  , cld
  , test
  , sub
  , xor
  , sar
  , sal
  , shr
  , shl
  ] ++ jcc_instructions

end x86

open x86

def main : io unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
