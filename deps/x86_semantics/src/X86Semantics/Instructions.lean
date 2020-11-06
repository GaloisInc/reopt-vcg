import X86Semantics.Common
-- import system.io

namespace x86

------------------------------------------------------------------------
-- Notation

open mc_semantics
open mc_semantics.type
open reg
open semantics

-- set_option class.instance_max_depth 1000

-- Introduces notation x[h..l] to slice the h..l bits out of x.
-- local
notation:1025 x "[[" h ".." l "]]" => slice x h l



infix:50 " ≠ " => neq

-- local
infix:50 " = " => eq

-- local
prefix:1024 "⇑" => lhs.expr

-- local 
abbrev ℕ := Nat

infix:40 " .= " => set

--notation d `.=` a `|` s :20 => set_aligned d s a

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

infixl:65 " .|. " => or
infixl:70 " .&. " => and

------------------------------------------------------------------------
-- utility functions

def nat_to_bv {w:ℕ} (n:ℕ) : bv w := expression.primitive $ prim.bv_nat w n

def undef {tp:type} : expression tp := expression.undef tp

def set_result_flags {w:ℕ} (res : expression (bv w)) : semantics Unit := do
  sf .= msb res
  zf .= (res = 0)
  pf .= even_parity (least_byte res)

def set_bitwise_flags {w:ℕ} (res : expression (bv w)) : semantics Unit := do
  of .= bit_zero
  cf .= bit_zero
  af .= undef
  set_result_flags res

def ssbb_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (borrow : expression bit) : expression bit := 
  prim.ssbb_overflows w dest src borrow
def ssub_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit := 
  ssbb_overflows dest src bit_zero

def usbb_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (borrow : expression bit) : expression bit :=
  prim.usbb_overflows w dest src borrow
def usub_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit :=
  usbb_overflows dest src bit_zero
def usub4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit :=
  usub_overflows (least_nibble dest) (least_nibble src)

def uadc_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : expression bit :=
  prim.uadc_overflows w dest src carry
def uadc4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : expression bit :=
  uadc_overflows (least_nibble dest) (least_nibble src) carry
def uadd_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit :=
  uadc_overflows dest src bit_zero
def uadd4_overflows {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit :=
  uadd_overflows (least_nibble dest) (least_nibble src)

def sadc_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) (carry : expression bit) : expression bit :=
  prim.sadc_overflows w dest src carry
def sadd_overflows  {w:ℕ} (dest : expression (bv w)) (src : expression (bv w)) : expression bit :=
  sadc_overflows dest src bit_zero

def do_xchg {w:ℕ} (addr1 : expression (bv w)) (addr2 : expression (bv w)) : semantics Unit :=
  record_event (event.xchg addr1 addr2)

def mux {tp:type} (c:bit) (t f : tp) : tp := prim.mux tp c t f

------------------------------------------------------------------------
-- imul and mul definitions

def set_overflow (be:bit) : semantics Unit := do
  let b ← eval be
  cf .= b
  of .= b
  sf .= undef
  zf .= undef
  af .= undef
  pf .= undef

def imul : instruction :=
 definst "imul" $ do
   instr_pat $ fun (src : expression (bv 8)) => 
     let action : semantics Unit := do
       let tmp ← eval $ sext al.expr 16 * sext src _
       ax .= tmp
       set_overflow $ sext (tmp[[7..0]]) _ ≠ tmp
     action
   instr_pat $ fun (src : expression (bv 16)) => 
     let action : semantics Unit := do
       let tmp ← eval $ sext ax.expr 32 * sext src _
       dx .= tmp[[31..16]]
       ax .= tmp[[15.. 0]]
       set_overflow $ sext (tmp[[15..0]]) _ ≠ tmp
     action
   instr_pat $ fun (src : expression (bv 32)) => 
     let action : semantics Unit := do
       let tmp ← eval $ sext eax.expr 64 * sext src _
       edx .= tmp[[63..32]]
       eax .= tmp[[31.. 0]]
       set_overflow $ sext tmp[[31..0]] _ ≠ tmp
     action
   instr_pat $ fun (w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp     ← eval $ sext dest.expr (2*w) * sext src (2*w)
       let tmp_low ← eval $ trunc tmp w
       dest .= tmp_low
       set_overflow $ sext tmp_low (2*w) ≠ tmp
     action
   instr_pat $ fun (w : one_of [16,32,64]) (dest : lhs (bv w)) (src1 src2 : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp     ← eval $ sext src1 (2*w) * sext src2 (2*w)
       let tmp_low ← eval $ trunc tmp w
       dest .= tmp_low
       set_overflow $ sext tmp_low (2*w) ≠ tmp
     action


def mul : instruction := do
 definst "mul" $ do
   instr_pat $ fun (src : expression (bv 8)) =>
     let action : semantics Unit := do
       let tmp ← eval $ uext al.expr 16 * uext src 16
       ax .= tmp
       set_overflow $ tmp[[16..8]] ≠ 0
     action
   instr_pat $ fun (src : expression (bv 16)) =>
     let action : semantics Unit := do
       let tmp ← eval $ uext ax.expr 32 * uext src _
       dx .= tmp[[31..16]]
       ax .= tmp[[15.. 0]]
       set_overflow $ tmp[[31..16]] ≠ 0
     action
   instr_pat $ fun (src : expression (bv 32)) =>
     let action : semantics Unit := do
       let tmp ← eval $ uext eax.expr 64 * uext src _
       edx .= tmp[[63..32]]
       eax .= tmp[[31.. 0]]
       set_overflow $ tmp[[63..32]] ≠ 0
     action
   instr_pat $ fun (src : expression (bv 64)) =>
     let action : semantics Unit := do
       let tmp ← eval $ uext rax.expr 128 * uext src _
       rdx .= tmp[[127..64]]
       rax .= tmp[[63..0]]
       set_overflow $ tmp[[127..64]] ≠ 0
     action

------------------------------------------------------------------------
-- mov definition

def mov : instruction := do
 definst "mov" $ do
   instr_pat $ fun (w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       dest .= src
     action

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
   instr_pat $ fun (w : one_of [16,32,64]) (u : one_of [8, 16, 32]) (dest : lhs (bv w)) (src : expression (bv u)) =>
     let action : semantics Unit := do
       dest .= sext src w
     action

------------------------------------------------------------------------
-- movsxd definition
-- Move with Sign-Extension
/-
def movsxd : instruction := do
 definst "movsxd" $ do
   pattern fun (w : one_of [16 =>32,64]) (u : one_of [16, 32]) (dest : lhs (bv w)) (src : bv u), do
     dest .= sext src w
-/
------------------------------------------------------------------------
-- movzx definition
-- Move with Zero-Extend

def movzx : instruction := do
 definst "movzx" $ do
   instr_pat $ fun (w : one_of [16,32,64]) (u : one_of [8, 16]) (dest : lhs (bv w)) (src : expression (bv u)) =>
     let action : semantics Unit := do
       dest .= uext src w
     action

------------------------------------------------------------------------
-- movdqa definition
-- Move Aligned Packed Integer Values

def movdqa : instruction := do
 definst "movdqa" $ do
   instr_pat $ fun (n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : expression (vec n (bv 32))) =>
     let action : semantics Unit := do
       set_aligned dest src 16
     action

------------------------------------------------------------------------
-- movaps definition
-- Move Aligned Packed Single-Precision Floating-Point Values

def movaps : instruction := do
 definst "movaps" $ do
   instr_pat $ fun (n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : expression (vec n (bv 32))) =>
     let action : semantics Unit := do
       set_aligned dest src 16
     action

------------------------------------------------------------------------
-- movups definition
-- Move Aligned Packed Single-Precision Floating-Point Values

def movups : instruction := do
 definst "movups" $ do
   instr_pat $ fun (n : one_of [4, 8, 16]) (dest : lhs (vec n (bv 32))) (src : expression (vec n (bv 32))) =>
     let action : semantics Unit := do
       set dest src
     action

------------------------------------------------------------------------
-- xchg definition
-- Exchange Register/Memory with Register
def xchg : instruction := do
 definst "xchg" $ do
   instr_pat $ fun (w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : lhs (bv w)) =>
     let action : semantics Unit := do
       do_xchg dest.expr src.expr
     action

------------------------------------------------------------------------
-- cmp definition
-- Compare Two Operands

def do_cmp {u v : Nat} (x : expression (bv u)) (src2 : expression (bv v)) : semantics Unit := do
  let y ← eval (sext src2 u)
  of .= ssub_overflows x y
  af .= usub4_overflows x y
  cf .= usub_overflows x y
  set_result_flags (x - y)

def cmp : instruction := do
  definst "cmp" $ do
    instr_pat $ fun (u v : one_of [8,16,32,64]) (x : expression (bv u)) (src2 : expression (bv v)) => do_cmp x src2
    instr_pat $ fun (x : imm (bv 8))  => do_cmp (⇑ al)  (expression.imm x)
    instr_pat $ fun (x : imm (bv 16)) => do_cmp (⇑ ax)  (expression.imm x)
    instr_pat $ fun (x : imm (bv 32)) => do_cmp (⇑ eax) (expression.imm x)
    instr_pat $ fun (x : imm (bv 64)) => do_cmp (⇑ rax) (expression.imm x)
 
--   pattern (u : one_of [8,16,32,64]) (x : imm (bv u)) := do
     


------------------------------------------------------------------------
-- cmpxchg definition
-- Compare and Exchange

/-

This instruction should be fairly straigth forward in the register-only
case, but requires more care for the memory case. We will probably also
need a notion of muxing on a bit.

def cmpxchg : instruction := do
 definst "cmpxchg" $ do
   pattern fun (dest : lhs (bv 8)) (src : bv 8) => do
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
   instr_pat $ fun (w : one_of [8, 16,32,64]) (value : lhs (bv w)) =>
     let action : semantics Unit := do
       let temp ← eval $ (⇑ value) - 1
       of .= ssub_overflows temp 1
       af .= usub4_overflows temp 1
       set_result_flags temp
       value .= temp
     action

------------------------------------------------------------------------
-- inc definition
-- Increment by 1

def inc : instruction := do
 definst "inc" $ do
   instr_pat $ fun (w : one_of [8, 16,32,64]) (value : lhs (bv w)) =>
     let action : semantics Unit := do
       let temp ← eval $ (⇑ value) + 1
       of .= sadd_overflows temp 1
       af .= uadd4_overflows temp 1
       set_result_flags temp
       value .= temp
     action

------------------------------------------------------------------------
-- neg definition
-- Two's Complement Negation

def neg : instruction := do
 definst "neg" $ do
   instr_pat $ fun (w : one_of [8, 16,32,64]) (dest : lhs (bv w)) =>
     let action : semantics Unit := do
       cf .= (⇑ dest) = 0
       of .= ssub_overflows 0 (⇑ dest)
       af .= usub4_overflows 0 (⇑ dest)
       let r ← eval $ - (⇑ dest)
       set_result_flags r
       dest .= r
     action

------------------------------------------------------------------------
-- nop definition
-- No Operation

def nop : instruction := do
 definst "nop" $ do
   instr_pat $ 
     let action : semantics Unit := do
       (pure () : semantics Unit)
     action
   instr_pat $ fun (w : one_of [16, 32]) =>
     let action : semantics Unit := do
       (pure () : semantics Unit)
     action

def noopl : instruction := do
 definst "noopl" $ do
   instr_pat $ fun (_ : lhs (bv 32)) =>
     let action : semantics Unit := do
       (pure () : semantics Unit)
     action


------------------------------------------------------------------------
-- pause definition
-- Spin Loop Hint

def pause : instruction := do
 definst "pause" $ do
   instr_pat $
     let action : semantics Unit := do
       (pure () : semantics Unit)
     action

------------------------------------------------------------------------
-- div definition
-- Unsigned Divide

def pair_fst {x y : type} (e:pair x y) : x := prim.pair_fst x y e
def pair_snd {x y : type} (e:pair x y) : y := prim.pair_snd x y e

def set_undef (l:List (lhs bit)) : semantics Unit := do
  _ <- l.mapM (fun r => r .= undef); pure ()


def div : instruction := do
 definst "div" $ do
   -- TODO: would it be better to have a single div primitive?
   instr_pat $ fun (src : expression (bv 8)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.quotRem 8 (⇑ ax) src
       al .= pair_fst r
       ah .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 16)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.quotRem 16 (cat (⇑ dx) (⇑ ax)) src
       ax .= pair_fst r
       dx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 32)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.quotRem 32 (cat (⇑ edx) (⇑ eax)) src
       eax .= pair_fst r
       edx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 64)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.quotRem 64 (cat (⇑ rdx) (⇑ rax)) src
       rax .= pair_fst r
       rdx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action

------------------------------------------------------------------------
-- idiv definition
-- Signed Divide

def idiv : instruction := do
 definst "idiv" $ do
   -- TODO: would it be better to have a single div primitive?
   instr_pat $ fun (src : expression (bv 8)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.squotRem 8 (⇑ ax) src
       al .= pair_fst r
       ah .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 16)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.squotRem 16 (cat (⇑ dx) (⇑ ax)) src
       ax .= pair_fst r
       dx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 32)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.squotRem 32 (cat (⇑ edx) (⇑ eax)) src
       eax .= pair_fst r
       edx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action
   instr_pat $ fun (src : expression (bv 64)) =>
     let action : semantics Unit := do
       let r ← eval $ prim.quotRem 64 (cat (⇑ rdx) (⇑ rax)) src
       rax .= pair_fst r
       rdx .= pair_snd r
       set_undef [cf, of, sf, zf, af, pf]
     action

------------------------------------------------------------------------
-- and definition
-- Logical AND

def and_def : instruction := do
 definst "and" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ dest) .&. src
       set_bitwise_flags tmp
       dest .= tmp
     action

------------------------------------------------------------------------
-- not definition
-- One's Complement Negation

def not : instruction := do
 definst "not" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) =>
     let action : semantics Unit := do
       dest .= complement (⇑ dest)
     action

------------------------------------------------------------------------
-- or definition
-- Logical Inclusive OR

def or_def : instruction := do
 definst "or" $ do
   instr_pat $ fun (u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : expression (bv v)) =>
     let action : semantics Unit := do
       dest .= (⇑ dest) .|. sext src u
       af .= undef
       of .= bit_zero
       cf .= bit_zero
       set_result_flags (⇑ dest)
     action

------------------------------------------------------------------------
-- xor definition
-- Logical Exclusive OR

def xor_def : instruction := do
 definst "xor" $ do
   instr_pat $ fun (u v : one_of [8, 16, 32, 64]) (dest : lhs (bv u)) (src : expression (bv v)) =>
     let action : semantics Unit := do
       dest .= xor (⇑ dest) (sext src u)
       af .= undef
       of .= bit_zero
       cf .= bit_zero
       set_result_flags (⇑ dest)
     action

------------------------------------------------------------------------
-- test definition
-- Logical compare
def test : instruction :=
 definst "test" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (x y : expression (bv w)) =>
     let action : semantics Unit := do
       set_bitwise_flags (x .&. y)
     action

----------------------------------      --------------------------------------
-- bt definition
-- Bit Test

def bt : instruction := do
 definst "bt" $ do
   instr_pat $ fun (wr : one_of [16, 32, 64]) (wi : one_of [8,16, 32, 64]) (base : reg (bv wr)) (idx : expression (bv wi)) =>
     let action : semantics Unit := do
       cf .= expression.bit_test (expression.of_reg base) idx
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
     action
   instr_pat $ fun (w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : reg (bv w)) =>
     let action : semantics Unit := do
       let i := sext (expression.of_reg idx : bv w) 64
       let addr ← eval $ expression.of_addr base + expression.mulc (w/8) (expression.quotc w i)
       cf .= expression.bit_test (expression.read (bv w) addr) (expression.of_reg idx)
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
     action
   instr_pat $ fun (w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : imm (bv 8)) =>
     let action : semantics Unit := do
       cf .= expression.bit_test (expression.read_addr base) (expression.imm idx)
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
     action

------------------------------------------------------------------------
-- btX definition

-- Type for functions for setting bits.
def bitf := ∀(w:one_of [16,32,64]) (j:ℕ), prim (fn (bv w) (fn (bv j) (bv w)))

-- Common function  for btc,btr and bts.
def btX (nm:String) (f: bitf) : instruction := do
 definst nm $ do
   instr_pat $ fun (wr : one_of [16, 32, 64]) (wi : one_of [8,16, 32, 64]) (base : reg (bv wr)) (idx : expression (bv wi)) =>
     let action : semantics Unit := do
       cf .= expression.bit_test (expression.of_reg base) idx
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
       lhs.of_reg base .= f wr wi (expression.of_reg base) idx
     action
   instr_pat $ fun (w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : reg (bv w)) =>
     let action : semantics Unit := do
       let i := sext (expression.of_reg idx : bv w) 64
       let addr ← eval $ expression.of_addr base + expression.mulc (w/8) (expression.quotc w i)
       cf .= expression.bit_test (expression.read (bv w) addr) (expression.of_reg idx)
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
       lhs.write_addr addr (bv w) .= f w w (expression.read (bv w) addr) (expression.of_reg idx)
     action
   instr_pat $ fun (w : one_of [16, 32, 64]) (base : addr (bv w)) (idx : imm (bv 8)) =>
     let action : semantics Unit := do
       let val ← eval (expression.read_addr base)
       cf .= expression.bit_test val (expression.imm idx)
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
       lhs.of_addr base .= f w 8 val (expression.imm idx)
     action

-- Bit test and complement
def btc : instruction := btX "btc" prim.btc
-- Bit test and reset
def btr : instruction := btX "btr" prim.btr
-- Bit test and set
def bts : instruction := btX "bts" prim.bts

------------------------------------------------------------------------
-- bsf definition
-- Bit Scan Forward

def bsf_def : instruction := do
 definst "bsf" $ do
   instr_pat $ fun (w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : expression (bv w)) =>
     let action : semantics Unit := do
       cf .= undef
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
       zf .= y = 0
       r .= bsf y
     action

------------------------------------------------------------------------
-- bsr definition
-- Bit Scan Reverse

def bsr_def : instruction := do
 definst "bsr" $ do
   instr_pat $ fun (w : one_of [16, 32, 64]) (r : lhs (bv w)) (y : expression (bv w)) =>
     let action : semantics Unit := do
       cf .= undef
       of .= undef
       sf .= undef
       af .= undef
       pf .= undef
       zf .= y = 0
       r .= bsr y
     action

------------------------------------------------------------------------
-- bswap definition
-- Byte Swap

def bswap : instruction := do
 definst "bswap" $ do
   instr_pat $ fun (w : one_of [32, 64]) (dest : lhs (bv w)) =>
     let action : semantics Unit := do
       dest .= expression.bswap (⇑ dest)
     action

------------------------------------------------------------------------
-- add definition

def add : instruction := do
 definst "add" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ dest) + src
       set_result_flags tmp
       cf .= uadd_overflows tmp src
       of .= sadd_overflows tmp src
       af .= uadd4_overflows tmp src
       dest .= tmp
     action
   -- FIXME: this gets around a limitation where the rax is implicit
   instr_pat $ fun (src : expression (bv 64)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ rax) + src
       set_result_flags tmp
       cf .= uadd_overflows tmp src
       of .= sadd_overflows tmp src
       af .= uadd4_overflows tmp src
       rax .= tmp
     action

------------------------------------------------------------------------
-- adc definition
-- Add with Carry

def adc : instruction := do
 definst "adc" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp ← eval $ expression.adc (⇑ dest) src cf
       set_result_flags tmp
       cf .= uadc_overflows  tmp src cf
       of .= sadc_overflows  tmp src cf
       af .= uadc4_overflows tmp src cf
       dest .= tmp
     action

------------------------------------------------------------------------
-- xadd definition
-- Exchange and Add

def xadd : instruction := do
 definst "xadd" $ do
   instr_pat fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : lhs (bv w)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ dest) + (⇑ src)
       src .= (⇑ dest)
       set_result_flags tmp
       cf .= uadd_overflows  tmp src
       of .= sadd_overflows  tmp src
       af .= uadd4_overflows tmp src
       dest .= tmp
     action

------------------------------------------------------------------------
-- fadd definition

def fadd : instruction := do
 definst "fadd" $ do
   instr_pat $ fun (dest : lhs x86_80) (src : lhs x86_80) => 
     let action : semantics Unit := do
       dest .= x87_fadd dest src
     action
   instr_pat $ fun (src : lhs float) =>
     let action : semantics Unit := do
       st0  .= x87_fadd st0 src
     action
   instr_pat $ fun (src : lhs double) =>
     let action : semantics Unit := do
       st0  .= x87_fadd st0 src
     action

------------------------------------------------------------------------
-- faddp definition

def faddp : instruction := do
 definst "faddp" $ do
   instr_pat $ fun (dest : lhs x86_80) (src : lhs x86_80) =>
     let action : semantics Unit := do
       dest .= x87_fadd dest src
       record_event event.pop_x87_register_stack
     action


------------------------------------------------------------------------
-- fiadd definition

def fiadd : instruction := do
 definst "fiadd" $ do
   instr_pat $ fun (w : one_of [16, 32]) (src : lhs (bv w)) =>
     let action : semantics Unit := do
       st0 .= x87_fadd st0 src
     action

------------------------------------------------------------------------
-- syscall definition

def syscall : instruction :=
  definst "syscall" $ mk_pattern (record_event event.syscall)

------------------------------------------------------------------------
-- cpuid definition

def cpuid : instruction :=
  definst "cpuid" $ mk_pattern (record_event event.cpuid)

------------------------------------------------------------------------
-- hlt definition
-- Halt

def hlt : instruction :=
  definst "hlt" $ mk_pattern (record_event event.hlt)

------------------------------------------------------------------------
-- sub definition

def sub_def : instruction := do
 definst "sub" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ dest) - src
       set_result_flags tmp
       cf .= usub_overflows tmp src
       of .= ssub_overflows tmp src
       af .= usub4_overflows tmp src
       dest .= tmp
     action
   instr_pat $ fun (src : expression (bv 64)) =>
     let action : semantics Unit := do
       let tmp ← eval $ (⇑ rax) - src
       set_result_flags tmp
       cf .= usub_overflows tmp src
       of .= ssub_overflows tmp src
       af .= usub4_overflows tmp src
       rax .= tmp
     action

------------------------------------------------------------------------
-- lea definition
-- Load Effective Address

def lea : instruction :=
 definst "lea" $ do
   instr_pat $ fun (w : one_of [16, 32, 64]) (dest : lhs (bv w)) (src : addr (bv 64)) =>
     let action : semantics Unit := do
       dest .= trunc (expression.of_addr src) w
     action

------------------------------------------------------------------------
-- call definition
-- Call Procedure

def call : instruction :=
 definst "call" $ do
   instr_pat $ fun (v : expression (bv 64)) =>
     let action : semantics Unit := do
       record_event (event.call v)
     action

------------------------------------------------------------------------
-- jmp definition
-- Jump
def jmp : instruction :=
 definst "jmp" $ do
   instr_pat $ fun (v : expression (bv 64)) =>
     let action : semantics Unit := do
       record_event (event.jmp v)
     action

------------------------------------------------------------------------
-- Condition codes
--
-- Conditional codes for instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.

def condition_codes : List (List String × expression bit)  := 
 [ -- Jump if above (cf = 0 and zf = 0)
   (["a", "nbe"], expression.bit_and ((cf : expression bit) = bit_zero) ((zf : expression bit) = bit_zero))
   -- Jump if above or equal (cf = 0)
 , (["ae", "nb", "nc"], (cf : expression bit) = bit_zero)
   -- Jump if below (cf = 1)
 , (["b", "c", "nae"], (cf : expression bit))
   -- Jump if below or equal (cf = 1 or zf = 1)
 , (["be"], expression.bit_or (cf : expression bit) (zf : expression bit))
   -- Jump if CX is 0
 , (["cxz"], (cx : expression (bv (gpreg_type.width gpreg_type.reg16))) = 0)
   -- Jump if ECX is 0
 , (["ecxz"], (ecx : expression (bv (gpreg_type.width gpreg_type.reg32))) = 0)
   -- Jump if RCX is 0
 , (["rcxz"], (rcx : expression (bv (gpreg_type.width gpreg_type.reg64))) = 0)
   -- Jump if equal (zf = 1)
 , (["e", "z"], (zf : expression bit))
   -- Jump if greater (zf = 0 and sf = of)
 , (["g", "nle"], expression.bit_and ((zf : expression bit) = bit_zero) ((sf : expression bit) = (of : expression bit)))
   -- Jump if greater or equal (sf = of)
 , (["ge", "nl"], (sf : expression bit) = (of : expression bit))
   -- Jump if less (sf ≠ of)
 , (["l", "nge"], (sf : expression bit) ≠ (of : expression bit))
   -- Jump if less or equal (zf = 1 or sf ≠ of)
 , (["le", "ng"], expression.bit_or (expression.of_lhs zf = bit_one) (expression.of_lhs sf ≠ expression.of_lhs of))
   -- Jump if not above (cf = 1 or zf = 1)
 , (["na"], expression.bit_or (expression.of_lhs cf = bit_one) (expression.of_lhs zf = bit_one))
   -- Jump if not equal (zf = 0)
 , (["ne", "nz"], expression.of_lhs zf = bit_zero)
   -- Jump if not overflow (of = 0)
 , (["no"], expression.of_lhs of = bit_zero)
   -- Jump if not parity (pf = 0)
 , (["np", "po"], expression.of_lhs pf = bit_zero)
   -- Jump if not sign (sf = 0)
 , (["ns"], expression.of_lhs sf = bit_zero)
   -- Jump if overflow (of = 1)
 , (["o"], expression.of_lhs of = bit_one)
   -- Jump if parity (pf = 1)
 , (["p", "pe"], expression.of_lhs pf = bit_one)
   -- Jump if sign (sf = 1)
 , (["s"], expression.of_lhs sf = bit_one)
 ]

------------------------------------------------------------------------
-- Jcc definition
-- Conditional jumps

def mk_jcc_instruction : String × expression bit → instruction
 | (name, cc) => definst ("j" ++ name) $ do
   instr_pat $ fun (addr : expression (bv 64)) =>
     let action : semantics Unit := do
       record_event (event.branch cc addr)
     action

def mk_jcc_instruction_aliases : List String × expression bit → List instruction
 | (names, cc) => List.map (fun n => mk_jcc_instruction (n, cc)) names

-- Conditional jump instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.
def jcc_instructions : List instruction := 
  List.join $ List.map mk_jcc_instruction_aliases condition_codes

------------------------------------------------------------------------
-- SETcc definition
-- Conditional sets

def mk_setcc_instruction : String × expression bit → instruction
 | (name, cc) => definst ("set" ++ name) $ do
 instr_pat $ fun (dest : lhs (bv 8)) =>
   let action : semantics Unit := do
     dest .= mux cc 0 1
   action

def mk_setcc_instruction_aliases : List String × expression bit → List instruction
 | (names, cc) => List.map (fun n => mk_setcc_instruction (n, cc)) names

-- Conditional jump instructions, some of these have multiple names. They only vary
-- in the condition checked so we use helper functions to associate mnemonics with
-- the conditions instead of defining each instruction at the top level.
-- TODO: We might be able to remove the aliases. It looks like the instruction encodings are the same
-- so it might suffice to find out what the decoder will pick as the canonical mnemonic.
def setcc_instructions : List instruction := 
  List.join $ List.map mk_setcc_instruction_aliases condition_codes

------------------------------------------------------------------------
-- CMOVcc definition
-- Conditional moves

def mk_cmovcc_instruction : String × expression bit → instruction
 | (name, cc) => definst ("cmov" ++ name) $ do
   instr_pat $ fun (w : one_of [8,16,32,64]) (dest : lhs (bv w)) (src : expression (bv w)) =>
     let action : semantics Unit := do
       set_cond dest cc src
     action

def mk_cmovcc_instruction_aliases : List String × expression bit → List instruction
 | (names, cc) => List.map (fun n => mk_cmovcc_instruction (n, cc)) names

def cmovcc_instructions : List instruction := 
  List.join $ List.map mk_cmovcc_instruction_aliases condition_codes

------------------------------------------------------------------------
-- leave definition
-- High Level Procedure Exit

def leave : instruction :=
 definst "leave" $ do
   instr_pat $ 
     let action : semantics Unit := do
       rsp .= rbp
       let v ← eval (expression.read (bv 64) (⇑ rsp))
       rsp .= rsp + nat_to_bv 8
       rbp .= v
     action

------------------------------------------------------------------------
-- pop definition

-- Pop a Value from the Stack
def pop_def : instruction :=
 definst "pop" $ do
   instr_pat $ fun (w : one_of [16, 32, 64]) (dest: lhs (bv w)) =>
     let action : semantics Unit := do
       let v ← eval (expression.read (bv w) (⇑ rsp))
       rsp  .= rsp + nat_to_bv (w/8)
       dest .= v
     action

------------------------------------------------------------------------
-- push definition
-- Push Word => doubleword or Quadword Onto the Stack
 
def push_def : instruction :=
 definst "push" $ do
   instr_pat $ fun (w : one_of [8, 16, 32, 64]) (value: expression (bv w)) =>
     let action : semantics Unit := do
       rsp .= rsp - nat_to_bv (w/8)
       lhs.write_addr (⇑ rsp) _ .= value
     action


------------------------------------------------------------------------
-- ret definition
-- Return from Procedure
def ret : instruction :=
 definst "retq" $ do
   instr_pat $ 
     let action : semantics Unit := do
       let addr ← eval $ expression.read (bv 64) (⇑ rsp)
       rsp .= rsp + nat_to_bv 8
       record_event (event.jmp addr)
     action
   instr_pat $ fun (off : expression (bv 16)) =>
     let action : semantics Unit := do
       let addr ← eval $ expression.read (bv 64) (⇑ rsp)
       rsp .= rsp + (nat_to_bv 8 + uext off 64)
       record_event (event.jmp addr)
     action

------------------------------------------------------------------------
-- cbw definition
-- Convert Byte to Word
def cbw : instruction :=
 definst "cbw" $ do
   instr_pat $ 
     let action : semantics Unit := do
       ax .= sext (⇑ al) 16
     action

------------------------------------------------------------------------
-- cdq definition
-- Convert Doubleword to Quadword
def cdq : instruction :=
 definst "cdq" $ do
   instr_pat $ 
     let action : semantics Unit := do
       let quadword := sext (⇑ eax) 64
       edx .= quadword[[63..32]]
     action

------------------------------------------------------------------------
-- cdqe definition
-- Convert Doubleword to Quadword
def cdqe : instruction :=
 definst "cdqe" $ do
   instr_pat $
     let action : semantics Unit := do
       rax .= sext (⇑ eax) 64
     action

------------------------------------------------------------------------
-- clc definition
-- Clear Carry Flag
def clc : instruction :=
 definst "clc" $ do
   instr_pat $
     let action : semantics Unit := do
       cf .= bit_zero
     action

------------------------------------------------------------------------
-- cld definition
-- Clear Direction Flag
def cld : instruction :=
 definst "cld" $ do
   instr_pat $
     let action : semantics Unit := do
       df .= bit_zero
     action

------------------------------------------------------------------------
-- cqo definition
-- Convert Quadword to Octword
def cqo : instruction :=
 definst "cqo" $ do
   instr_pat $
     let action : semantics Unit := do
       let octword := sext (⇑ rax) 128
       rdx .= octword[[127..64]]
     action

------------------------------------------------------------------------
-- cwd definition
-- Convert Word to Doubleword
def cwd : instruction :=
 definst "cwd" $ do
   instr_pat $
     let action : semantics Unit := do
       let doubleword := sext (⇑ ax) 32
       dx .= doubleword[[31..16]]
     action

------------------------------------------------------------------------
-- cwde definition
-- Convert Word to Doubleword
def cwde : instruction :=
 definst "cwde" $ do
   instr_pat $
     let action : semantics Unit := do
       eax .= sext (⇑ ax) 32
     action


------------------------------------------------------------------------
-- sar/shr/sal/shl definitions

/- This is an enum for the shift op, so that our shift code can reflect the Intel description. -/
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
          : semantics Unit := do
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  let low_count ← eval $ count .&. count_mask
  -- compute the result
  let res ← eval $
    match op with
    | shift_op.shl => prim.shl w v low_count
    | shift_op.shr => prim.shr w v low_count
    | shift_op.sar => prim.sar w v low_count

  -- When the count is zero, nothing happens, and no flags change
  let is_nonzero : expression bit := low_count ≠ 0
  -- Set the af flag
  set_cond af is_nonzero undef
  match op with
  | shift_op.shl =>
     cf .= prim.shl_carry w cf v low_count
  | shift_op.shr => do
     cf .= prim.shr_carry w v cf low_count
  | shift_op.sar => do
     cf .= prim.sar_carry w v cf low_count

  -- Compute value of of_flag if low_count is 1.
  let of_flag :=
    match op with
    | shift_op.shl => expression.bit_xor (@msb w res) (@msb w (⇑ v))
    | shift_op.sar => bit_zero
    | shift_op.shr => @msb w (⇑ v)

  set_cond of is_nonzero (mux (low_count = 1) of_flag undef)
  set_cond sf is_nonzero (msb res)
  set_cond zf is_nonzero (res = 0)
  set_cond pf is_nonzero (even_parity (least_byte res))
  set_cond v  is_nonzero res

def shift_def (nm:String) (o : shift_op) : instruction :=
  definst nm $ do
    instr_pat $ fun (w : one_of [8, 16, 32]) (value: lhs (bv w)) (count: expression (bv 8)) =>
      let action : semantics Unit := do
        do_sh o value count ((32 - 1) : expression (bv 8))
      action
    instr_pat $ fun (value: lhs (bv 64)) (count: expression (bv 8)) =>
      let action : semantics Unit := do
        do_sh o value count ((64 - 1) : expression (bv 8))
      action
    -- CL version
    instr_pat $ fun (w : one_of [8, 16, 32]) (value: lhs (bv w)) =>
      let action : semantics Unit := do
        do_sh o value (⇑ cl) ((32 - 1) : expression (bv 8))
      action
    instr_pat $ fun (value: lhs (bv 64)) =>
      let action : semantics Unit := do
        do_sh o value (⇑ cl) ((64 - 1) : expression (bv 8))
      action

-- Shift logical right
def shr_def : instruction := shift_def "shr" shift_op.shr

-- Shift arithmetic right
def sar_def : instruction := shift_def "sar" shift_op.sar

-- Shift logical left
def shl_def : instruction := shift_def "shl" shift_op.shl

-- Shift arithmetic left (same as shl semantically)
def sal_def : instruction := shift_def "sal" shift_op.shl

------------------------------------------------------------------------
-- Instruction List

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
  , cpuid
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
  jcc_instructions ++ setcc_instructions ++ cmovcc_instructions ++
  [ jmp
  , lea
  , leave
  , mov
  , movaps
  , movups
  , movsx
  -- , movsxd
  , movzx
  , mul
  , neg
  , nop
  , noopl
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

def main : io Unit := do
  monad.mapm' (io.put_str_ln ∘ repr) all_instructions
-/
