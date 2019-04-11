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

--notation d `.=` a `|` s :20 := set_aligned d s a

------------------------------------------------------------------------
-- bitvector functions

def xor {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bv_xor w x y
def complement {w:ℕ} (b : bv w) : bv w := prim.bv_complement w b
def and {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bv_and w x y
def or {w:ℕ} (x : bv w) (y : bv w) : bv w := prim.bv_or w x y
def cat {w:ℕ} (x : bv w) (y : bv w) : bv (2*w) := prim.cat w x y
def least_nibble {w:ℕ} (x : bv w) : bv 4 := trunc x 4
def ule {w:ℕ} (x y : bv w) : bit := prim.ule w x y
def ult {w:ℕ} (x y : bv w) : bit := prim.ult w x y
def sub {w:ℕ} (x y : bv w) : bv w := prim.sub w x y

def msb {w:ℕ} (v : bv w) : bit := prim.msb w v
def least_byte {w:ℕ} (v : bv w) : bv 8 := trunc v 8
def even_parity {w:ℕ} (v : bv w) : bit := prim.even_parity w v

infixl `.|.`:65 := or
infixl `.&.`:70 := and

------------------------------------------------------------------------
-- utility functions

def nat_to_bv {w:ℕ} (n:ℕ) : bv w := prim.bv_nat w n

def undef {tp:type} : expression tp := expression.undef tp

def set_result_flags {w:ℕ} (res : bv w) : semantics unit := do
  sf .= msb res,
  zf .= res = 0,
  pf .= even_parity (least_byte res)

def set_bitwise_flags {w:ℕ} (res : bv w) : semantics unit := do
  of .= bit_zero,
  cf .= bit_zero,
  af .= undef,
  set_result_flags res

def ssbb_overflows  {w:ℕ} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.ssbb_overflows w dest src borrow
def ssub_overflows  {w:ℕ} (dest : bv w) (src : bv w)                : bit := ssbb_overflows dest src bit_zero

def usbb_overflows  {w:ℕ} (dest : bv w) (src : bv w) (borrow : bit) : bit := prim.usbb_overflows w dest src borrow
def usub_overflows  {w:ℕ} (dest : bv w) (src : bv w)                : bit := usbb_overflows dest src bit_zero
def usub4_overflows {w:ℕ} (dest : bv w) (src : bv w)                : bit := usub_overflows (least_nibble dest) (least_nibble src)

def uadc_overflows  {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.uadc_overflows w dest src carry
def uadc4_overflows {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := uadc_overflows (least_nibble dest) (least_nibble src) carry
def uadd_overflows  {w:ℕ} (dest : bv w) (src : bv w)               : bit := uadc_overflows dest src bit_zero
def uadd4_overflows {w:ℕ} (dest : bv w) (src : bv w)               : bit := uadd_overflows (least_nibble dest) (least_nibble src)

def sadc_overflows  {w:ℕ} (dest : bv w) (src : bv w) (carry : bit) : bit := prim.sadc_overflows w dest src carry
def sadd_overflows  {w:ℕ} (dest : bv w) (src : bv w)               : bit := sadc_overflows dest src bit_zero

def do_xchg {w:ℕ} (addr1 : bv w) (addr2 : bv w) : semantics unit :=
  record_event (event.xchg addr1 addr2)

def mux {tp:type} (c:bit) (t f : tp) : tp := prim.mux tp c t f

------------------------------------------------------------------------
-- imul and mul definitions

def set_overflow (be:bit) : semantics unit := do
  b ← eval be,
  cf .= b,
  of .= b,
  sf .= undef,
  zf .= undef,
  af .= undef,
  pf .= undef

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
     set_aligned dest src 16
   pat_end

------------------------------------------------------------------------
-- movaps definition
-- Move Aligned Packed Single-Precision Floating-Point Values

def movaps : instruction := do
 definst "movaps" $ do
   pattern λ(n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : vec n (bv 32)), do
     set_aligned dest src 16
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
-- cmp definition
-- Compare Two Operands

def cmp : instruction := do
 definst "cmp" $ do
   pattern λ(u v : one_of [8,16,32,64]) (x : bv u) (src2 : bv v), do
     y ← eval (sext src2 u),
     of .= ssub_overflows x y,
     af .= usub4_overflows x y,
     cf .= usub_overflows x y,
     set_result_flags (x - y)
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
     cf .= ⇑dest = 0,
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

def pair_fst {x y : type} (e:pair x y) : x := prim.pair_fst x y e
def pair_snd {x y : type} (e:pair x y) : y := prim.pair_snd x y e

def set_undef (l:list (lhs bit)) : semantics unit := do
  l.mmap' (λr, r .= undef)


def div : instruction := do
 definst "div" $ do
   -- TODO: would it be better to have a single div primitive?
   pattern λ(src : bv 8), do
     r ← eval $ prim.quotRem 8 ⇑ax src,
     al .= pair_fst r,
     ah .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 16), do
     r ← eval $ prim.quotRem 16 (cat ⇑dx ⇑ax) src,
     ax .= pair_fst r,
     dx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 32), do
     r ← eval $ prim.quotRem 32 (cat ⇑edx ⇑eax) src,
     eax .= pair_fst r,
     edx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 64), do
     r ← eval $ prim.quotRem 64 (cat ⇑rdx ⇑rax) src,
     rax .= pair_fst r,
     rdx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end

------------------------------------------------------------------------
-- idiv definition
-- Signed Divide

def idiv : instruction := do
 definst "idiv" $ do
   -- TODO: would it be better to have a single div primitive?
   pattern λ(src : bv 8), do
     r ← eval $ prim.squotRem 8 ⇑ax src,
     al .= pair_fst r,
     ah .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 16), do
     r ← eval $ prim.squotRem 16 (cat ⇑dx ⇑ax) src,
     ax .= pair_fst r,
     dx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 32), do
     r ← eval $ prim.squotRem 32 (cat ⇑edx ⇑eax) src,
     eax .= pair_fst r,
     edx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end,
   pattern λ(src : bv 64), do
     r ← eval $ prim.quotRem 64 (cat ⇑rdx ⇑rax) src,
     rax .= pair_fst r,
     rdx .= pair_snd r,
     set_undef [cf, of, sf, zf, af, pf]
   pat_end

------------------------------------------------------------------------
-- and definition
-- Logical AND

def and_def : instruction := do
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
     dest .= complement ⇑dest
   pat_end

------------------------------------------------------------------------
-- or definition
-- Logical Inclusive OR

def or_def : instruction := do
 definst "or" $ do
   pattern λ(u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : bv v), do
     dest .= ⇑dest .|. sext src u,
     af .= undef,
     of .= bit_zero,
     cf .= bit_zero,
     set_result_flags ⇑dest
   pat_end

------------------------------------------------------------------------
-- xor definition
-- Logical Exclusive OR

def xor_def : instruction := do
 definst "xor" $ do
   pattern λ(u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : bv v), do
     dest .= xor ⇑dest (sext src u),
     af .= undef,
     of .= bit_zero,
     cf .= bit_zero,
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

----------------------------------      --------------------------------------
-- bt definition
-- Bit Test

def bt : instruction := do
 definst "bt" $ do
   pattern λ(wr : one_of [16, 32, 64]) (wi : one_of [8,16, 32, 64]) (base : reg (bv wr)) (idx : bv wi), do
     cf .= expression.bit_test (expression.of_reg base) idx,
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : reg (bv w)), do
     let i := sext (expression.of_reg idx : bv w) 64,
     addr ← eval $ expression.of_addr base + expression.mulc (w/8) (expression.quotc w i),
     cf .= expression.bit_test (expression.read (bv w) addr) (expression.of_reg idx),
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : imm (bv 8)), do
     cf .= expression.bit_test (expression.read_addr base) (expression.imm idx),
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef
   pat_end

------------------------------------------------------------------------
-- btX definition

-- Type for functions for setting bits.
def bitf := Π(w:one_of [16,32,64]) (j:ℕ), prim (fn (bv w) (fn (bv j) (bv w)))

-- Common function  for btc,btr and bts.
def btX (nm:string) (f: bitf) : instruction := do
 definst nm $ do
   pattern λ(wr : one_of [16, 32, 64]) (wi : one_of [8,16, 32, 64]) (base : reg (bv wr)) (idx : bv wi), do
     cf .= expression.bit_test (expression.of_reg base) idx,
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef,
     lhs.of_reg base .= f wr wi (expression.of_reg base) idx
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : reg (bv w)), do
     let i := sext (expression.of_reg idx : bv w) 64,
     addr ← eval $ expression.of_addr base + expression.mulc (w/8) (expression.quotc w i),
     cf .= expression.bit_test (expression.read (bv w) addr) (expression.of_reg idx),
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef,
     lhs.write_addr addr (bv w) .= f w w (expression.read (bv w) addr) (expression.of_reg idx)
   pat_end,
   pattern λ(w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : imm (bv 8)), do
     val ← eval (expression.read_addr base),
     cf .= expression.bit_test val (expression.imm idx),
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef,
     lhs.of_addr base .= f w 8 val (expression.imm idx)
   pat_end

--- Bit test and complement
def btc : instruction := btX "btc" prim.btc
--- Bit test and reset
def btr : instruction := btX "btr" prim.btr
--- Bit test and set
def bts : instruction := btX "bts" prim.bts

------------------------------------------------------------------------
-- bsf definition
-- Bit Scan Forward

def bsf_def : instruction := do
 definst "bsf" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     cf .= undef,
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef,
     zf .= y = 0,
     r .= bsf y
  pat_end

------------------------------------------------------------------------
-- bsr definition
-- Bit Scan Reverse

def bsr_def : instruction := do
 definst "bsr" $ do
   pattern λ(w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : bv w), do
     cf .= undef,
     of .= undef,
     sf .= undef,
     af .= undef,
     pf .= undef,
     zf .= y = 0,
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

def sub_def : instruction := do
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
   pattern λ(v : bv 64), do
     record_event (event.call v)
   pat_end

------------------------------------------------------------------------
-- jmp definition
-- Jump
def jmp : instruction :=
 definst "jmp" $ do
   pattern λ(v : bv 64), do
     record_event (event.jmp v)
   pat_end

------------------------------------------------------------------------
-- Jcc definition
-- Conditional jumps

def mk_jcc_instruction : string × expression bit → instruction
 | (name, cc) := definst name $ do
 pattern λ(addr : bv 64), do
   record_event (event.branch cc addr)
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
   (["ja", "jnbe"], expression.bit_and ((cf : bit) = bit_zero) ((zf : bit) = bit_zero))
   -- Jump if above or equal (cf = 0)
 , (["jae", "jnb", "jnc"], (cf : bit) = bit_zero)
   -- Jump if below (cf = 1)
 , (["jb", "jc", "jnae"], (cf : bit))
   -- Jump if below or equal (cf = 1 or zf = 1)
 , (["jbe"], expression.bit_or (cf : bit) (zf : bit))
   -- Jump if CX is 0
 , (["jcxz"], (cx : bv 16) = 0)
   -- Jump if ECX is 0
 , (["jecxz"], (ecx : bv 32) = 0)
   -- Jump if RCX is 0
 , (["jrcxz"], (rcx : bv 64) = 0)
   -- Jump if equal (zf = 1)
 , (["je", "jz"], (zf : bit))
   -- Jump if greater (zf = 0 and sf = of)
 , (["jg", "jnle"], expression.bit_and ((zf : bit) = bit_zero) ((sf : bit) = (of : bit)))
   -- Jump if greater or equal (sf = of)
 , (["jge", "jnl"], (sf : bit) = (of : bit))
   -- Jump if less (sf ≠ of)
 , (["jl", "jnge"], (sf : bit) ≠ (of : bit))
   -- Jump if less or equal (zf = 1 or sf ≠ of)
 , (["jle", "jng"], expression.bit_or (expression.of_lhs zf = bit_one) (expression.of_lhs sf ≠ expression.of_lhs of))
   -- Jump if not above (cf = 1 or zf = 1)
 , (["jna"], expression.bit_or (expression.of_lhs cf = bit_one) (expression.of_lhs zf = bit_one))
   -- Jump if not equal (zf = 0)
 , (["jne", "jnz"], expression.of_lhs zf = bit_zero)
   -- Jump if not overflow (of = 0)
 , (["jno"], expression.of_lhs of = bit_zero)
   -- Jump if not parity (pf = 0)
 , (["jnp", "jpo"], expression.of_lhs pf = bit_zero)
   -- Jump if not sign (sf = 0)
 , (["jns"], expression.of_lhs sf = bit_zero)
   -- Jump if overflow (of = 1)
 , (["jo"], expression.of_lhs of = bit_one)
   -- Jump if parity (pf = 1)
 , (["jp", "jpe"], expression.of_lhs pf = bit_one)
   -- Jump if sign (sf = 1)
 , (["js"], expression.of_lhs sf = bit_one)
 ]

------------------------------------------------------------------------
-- leave definition
-- High Level Procedure Exit

def leave : instruction :=
 definst "leave" $ do
   pattern do
     rsp .= rbp,
     v ← eval (expression.read (bv 64) rsp),
     rsp .= rsp + nat_to_bv 8,
     rbp .= v
   pat_end

------------------------------------------------------------------------
-- pop definition

-- Pop a Value from the Stack
def pop_def : instruction :=
 definst "pop" $ do
   pattern λ(w : one_of [16, 32, 64]) (dest: lhs (bv w)),do
     v ← eval (expression.read (bv w) rsp),
     rsp  .= rsp + nat_to_bv (w/8),
     dest .= v
   pat_end

------------------------------------------------------------------------
-- push definition
-- Push Word, Doubleword or Quadword Onto the Stack

def push_def : instruction :=
 definst "push" $ do
   pattern λ(w : one_of [8, 16, 32, 64]) (value: bv w),do
     rsp .= rsp - nat_to_bv (w/8),
     rsp .= uext value 64
   pat_end


------------------------------------------------------------------------
-- ret definition
-- Return from Procedure
def ret : instruction :=
 definst "ret" $ do
   pattern do
     addr ← eval $ expression.read (bv 64) rsp,
     rsp .= rsp + 8,
     record_event (event.jmp addr)
   pat_end,
   pattern λ(off : bv 16), do
     addr ← eval $ expression.read (bv 64) rsp,
     rsp .= rsp + (8 + uext off 64),
     record_event (event.jmp addr)
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
-- cdq definition
-- Convert Doubleword to Quadword
def cdq : instruction :=
 definst "cdq" $ do
   pattern do
     let quadword := sext ⇑eax 64, do
     edx .= quadword[[63..32]]
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
     cf .= bit_zero
   pat_end

------------------------------------------------------------------------
-- cld definition
-- Clear Direction Flag
def cld : instruction :=
 definst "cld" $ do
   pattern do
     df .= bit_zero
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
-- cwd definition
-- Convert Word to Doubleword
def cwd : instruction :=
 definst "cwd" $ do
   pattern do
     let doubleword := sext ⇑ax 32, do
     dx .= doubleword[[31..16]]
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
-- sar/shr/sal/shl definitions

/-- This is an enum for the shift op, so that our shift code can reflect the Intel description. -/
inductive shift_op
| shl : shift_op -- Also used for shl since it is same operation.
| sar : shift_op
| shr : shift_op


-- Generic shift operation, takes functions for doing the shift and
-- setting the flags.
def do_sh {w:ℕ}
          (op : shift_op)
          (v: lhs (bv w))                -- value to be shifted
          (count: bv 8)                  -- amount to shift by
          (count_mask: bv 8)             -- mask for the counter
          : semantics unit := do
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  low_count ← eval $ count .&. count_mask,
  -- compute the result
  res ← eval $
        match op with
        | shift_op.shl := prim.shl w v low_count
        | shift_op.shr := prim.shr w v low_count
        | shift_op.sar := prim.sar w v low_count
        end,
  -- When the count is zero, nothing happens, and no flags change
  let is_nonzero := low_count ≠ 0,
  -- Set the af flag
  set_cond af is_nonzero undef,
  match op with
  | shift_op.shl :=
     cf .= prim.shl_carry w cf v low_count
  | shift_op.shr := do
     cf .= prim.shr_carry w v cf low_count
  | shift_op.sar := do
     cf .= prim.sar_carry w v cf low_count
  end,
  -- Compute value of of_flag if low_count is 1.
  let of_flag :=
        match op with
        | shift_op.shl := expression.bit_xor (@msb w res) (@msb w v)
        | shift_op.sar := bit_zero
        | shift_op.shr := @msb w v
        end,
  set_cond of is_nonzero (mux (low_count = 1) of_flag undef),
  set_cond sf is_nonzero (msb res),
  set_cond zf is_nonzero (res = 0),
  set_cond pf is_nonzero (even_parity (least_byte res)),
  set_cond v  is_nonzero res

def shift_def (nm:string) (o : shift_op) : instruction :=
  definst nm $ do
    pattern λ(w : one_of [8, 16, 32]) (value: lhs (bv w)) (count: bv 8),do
      do_sh o value count (32-1)
    pat_end,
    pattern λ(value: lhs (bv 64)) (count: bv 8), do
      do_sh o value count (64-1)
    pat_end

-- Shift logical right
def shr_def : instruction := shift_def "shr" shift_op.shr

-- Shift arithmetic right
def sar_def : instruction := shift_def "sar" shift_op.sar

-- Shift logical left
def shl_def : instruction := shift_def "shl" shift_op.shl

-- Shift arithmetic left (same as shl semantically)
def sal_def : instruction := shift_def "sal" shift_op.shl

------------------------------------------------------------------------
-- Instruction list

def all_instructions :=
  [ and_def
  , adc
  , add
  , bsf_def
  , bsr_def
  , bswap
  , bt
  , btc
  , btr
  , bts
  , call
  , cbw
  , cdq
  , cdqe
  , clc
  , cld
  , cmp
  , cqo
  , cwd
  , cwde
  , dec
  , div
  , fadd
  , faddp
  , fiadd
  , hlt
  , idiv
  , imul
  , inc
  ] ++
  jcc_instructions ++
  [ jmp
  , lea
  , leave
  , mov
  , movsx
  , movsxd
  , movzx
  , mul
  , neg
  , nop
  , not
  , or_def
  , pause
  , pop_def
  , push_def
  , ret
  , sal_def
  , sar_def
  , shl_def
  , shr_def
  , sub_def
  , syscall
  , test
  , xadd
  , xchg
  , xor_def
  ]

end x86

/-
open x86

def main : io unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
-/
