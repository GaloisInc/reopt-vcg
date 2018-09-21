import .common

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

local notation `⇑`:max x:max := coe1 x

local notation ℕ := nat_expr

infix `.=`:20 := set

------------------------------------------------------------------------
-- utility functions

def msb {w:ℕ} (v : bv w) : bit := sorry
def is_zero {w:ℕ} (v : bv w) : bit := sorry
def least_byte {w:ℕ} (v : bv w) : bv 8 := sorry
def even_parity {w:ℕ} (v : bv w) : bit := sorry

def set_undefined {tp:type} (v : lhs tp) : semantics unit := do
  semantics.add_action (action.mk_undef v)

def set_overflow (b:bit) : semantics unit := do
  cf .= b,
  of .= b,
  set_undefined sf,
  set_undefined zf,
  set_undefined af,
  set_undefined pf

def set_result_flags {w:ℕ} (res : value (bv w)) : semantics unit := do
  sf .= msb res,
  zf .= is_zero res,
  pf .= even_parity (least_byte res)

def uadd_overflows  {w:ℕ} (dest : value (bv w)) (src : value (bv w)) : bit := sorry
def uadd4_overflows {w:ℕ} (dest : value (bv w)) (src : value (bv w)) : bit := sorry
def sadd_overflows  {w:ℕ} (dest : value (bv w)) (src : value (bv w)) : bit := sorry

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

end x86
