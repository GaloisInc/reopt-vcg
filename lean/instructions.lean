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

------------------------------------------------------------------------
-- bitvector functions

-- `off` is the index of the bit to return.
-- TODO: figure out how to handle out of bounds and any other edge cases and document the
-- assumptions.
def bv_bit {w:ℕ} (base : bv w) (off : bv w) : bit := prim.bvbit w base off
def bv_xor {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.xor w x y
def bv_shl {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.shl w x y
def bv_complement {w:ℕ} (b : bv w) : bv w := prim.complement w b
def bv_is_zero {w:ℕ} (b : bv w) : bit := b = 0
def bv_and {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.and w x y
def bv_or {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.or w x y
def bv_cat {w:ℕ} (x : bv w) (y : bv w) : bv (2*w) := prim.bvcat w x y
def bv_least_nibble {w:ℕ} (x : bv w) : bv 4 := prim.bv_least_nibble w x

def msb {w:ℕ} (v : bv w) : bit := prim.msb w v
def least_byte {w:ℕ} (v : bv w) : bv 8 := prim.least_byte w v
def even_parity {w:ℕ} (v : bv w) : bit := prim.even_parity w v

infixl `.|.`:65 := bv_or
infixl `.&.`:70 := bv_and

------------------------------------------------------------------------
-- utility functions

def nat_to_bv {w:ℕ} (n:ℕ) : bv w := prim.bvnat w n

def set_undefined {tp:type} (v : lhs tp) : semantics unit := do
  semantics.add_action (action.mk_undef v)

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

def do_jmp (cond : bit) (addr : bv 64) : semantics unit :=
  match cond with
  | prim.one := record_event (event.jmp addr)
  | _        := return ()
  end

def do_xchg {w:ℕ} (addr1 : bv w) (addr2 : bv w) : semantics unit :=
  record_event (event.xchg addr1 addr2)

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
     do_jmp one (uext v 64)
   pat_end

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
  ]

end x86

open x86

def main : io unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
