/-
This module defines the core datatypes used to represent x86 instruction semantics.
-/
import Galois.Category.Coe1
-- import galois.sexpr

-- No lemma length (x :: xs) = succ (length xs)
-- namespace List

-- def get {a : Type}: forall (ls : List a) (n : Nat) (pf : n < ls.length), a
-- | x :: _, 0, _ => x
-- | (_ :: ls), (Nat.succ n), pf => ls.get n (Nat.ltOfSuccLtSucc pf)

-- end List

namespace mc_semantics

------------------------------------------------------------------------
-- arg_index

/- This denotes the index of a variable in a context.

It is equivant to a deBrujin level.
-/
@[reducible]
def arg_index := Nat

------------------------------------------------------------------------
-- one_of

inductive one_of (l:List Nat) : Type
| elem{} (v : Nat) : -- l.contains v
                    one_of

namespace one_of

-- FIXME: fix this when we get tactics
def to_nat {l:List Nat} : one_of l → Nat
| (one_of.elem x) => x

instance (l:List Nat) : HasCoe (one_of l) Nat :=
⟨ one_of.to_nat ⟩

end one_of

------------------------------------------------------------------------
-- Type

inductive type
| bv (w:Nat) : type
| bit : type
| float  : type
| double : type
| x86_80 : type
| vec (w:Nat) (tp:type) : type
-- A pair with fields of the given type.
-- N.B. We use pairs rather than more general tuples for now, just for simplicity.
-- We do not need this currently, but have left it available in case it is needed soon.
| pair (x y : type) : type
-- A function from arg to res
| fn (arg:type) (res:type) : type

namespace type

-- c.f. scripts/mk_dec_eq.hs
-- *MkDecEq> writeFile "typeDecEq" (mkDecEq "type" ctors_type "hasDecEq")
protected def hasDecEq : ∀(e e' : type), Decidable (e = e')
| (bv c1), (bv c1') => 
 (match decEq c1 c1' with 
  | (isTrue h1) => isTrue (h1 ▸ rfl)
  | (isFalse nh) => isFalse (fun h => type.noConfusion h $ fun h1' => absurd h1' nh))
| bit, bit => isTrue rfl
| float, float => isTrue rfl
| double, double => isTrue rfl
| x86_80, x86_80 => isTrue rfl
| (vec c1 c2), (vec c1' c2') => 
 (match decEq c1 c1', hasDecEq c2 c2' with 
  | (isTrue h1), (isTrue h2) => isTrue (h1 ▸ h2 ▸ rfl)
  | (isFalse nh), _ => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h1' nh)
  | (isTrue _), (isFalse nh) => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h2' nh))
| (pair c1 c2), (pair c1' c2') => 
 (match hasDecEq c1 c1', hasDecEq c2 c2' with 
  | (isTrue h1), (isTrue h2) => isTrue (h1 ▸ h2 ▸ rfl)
  | (isFalse nh), _ => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h1' nh)
  | (isTrue _), (isFalse nh) => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h2' nh))
| (fn c1 c2), (fn c1' c2') => 
 (match hasDecEq c1 c1', hasDecEq c2 c2' with 
  | (isTrue h1), (isTrue h2) => isTrue (h1 ▸ h2 ▸ rfl)
  | (isFalse nh), _ => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h1' nh)
  | (isTrue _), (isFalse nh) => isFalse (fun h => type.noConfusion h $ fun h1' h2' => absurd h2' nh))
| (bv _), bit => isFalse (fun h => type.noConfusion h)
| (bv _), float => isFalse (fun h => type.noConfusion h)
| (bv _), double => isFalse (fun h => type.noConfusion h)
| (bv _), x86_80 => isFalse (fun h => type.noConfusion h)
| (bv _), (vec _ _) => isFalse (fun h => type.noConfusion h)
| (bv _), (pair _ _) => isFalse (fun h => type.noConfusion h)
| (bv _), (fn _ _) => isFalse (fun h => type.noConfusion h)
| bit, (bv _) => isFalse (fun h => type.noConfusion h)
| bit, float => isFalse (fun h => type.noConfusion h)
| bit, double => isFalse (fun h => type.noConfusion h)
| bit, x86_80 => isFalse (fun h => type.noConfusion h)
| bit, (vec _ _) => isFalse (fun h => type.noConfusion h)
| bit, (pair _ _) => isFalse (fun h => type.noConfusion h)
| bit, (fn _ _) => isFalse (fun h => type.noConfusion h)
| float, (bv _) => isFalse (fun h => type.noConfusion h)
| float, bit => isFalse (fun h => type.noConfusion h)
| float, double => isFalse (fun h => type.noConfusion h)
| float, x86_80 => isFalse (fun h => type.noConfusion h)
| float, (vec _ _) => isFalse (fun h => type.noConfusion h)
| float, (pair _ _) => isFalse (fun h => type.noConfusion h)
| float, (fn _ _) => isFalse (fun h => type.noConfusion h)
| double, (bv _) => isFalse (fun h => type.noConfusion h)
| double, bit => isFalse (fun h => type.noConfusion h)
| double, float => isFalse (fun h => type.noConfusion h)
| double, x86_80 => isFalse (fun h => type.noConfusion h)
| double, (vec _ _) => isFalse (fun h => type.noConfusion h)
| double, (pair _ _) => isFalse (fun h => type.noConfusion h)
| double, (fn _ _) => isFalse (fun h => type.noConfusion h)
| x86_80, (bv _) => isFalse (fun h => type.noConfusion h)
| x86_80, bit => isFalse (fun h => type.noConfusion h)
| x86_80, float => isFalse (fun h => type.noConfusion h)
| x86_80, double => isFalse (fun h => type.noConfusion h)
| x86_80, (vec _ _) => isFalse (fun h => type.noConfusion h)
| x86_80, (pair _ _) => isFalse (fun h => type.noConfusion h)
| x86_80, (fn _ _) => isFalse (fun h => type.noConfusion h)
| (vec _ _), (bv _) => isFalse (fun h => type.noConfusion h)
| (vec _ _), bit => isFalse (fun h => type.noConfusion h)
| (vec _ _), float => isFalse (fun h => type.noConfusion h)
| (vec _ _), double => isFalse (fun h => type.noConfusion h)
| (vec _ _), x86_80 => isFalse (fun h => type.noConfusion h)
| (vec _ _), (pair _ _) => isFalse (fun h => type.noConfusion h)
| (vec _ _), (fn _ _) => isFalse (fun h => type.noConfusion h)
| (pair _ _), (bv _) => isFalse (fun h => type.noConfusion h)
| (pair _ _), bit => isFalse (fun h => type.noConfusion h)
| (pair _ _), float => isFalse (fun h => type.noConfusion h)
| (pair _ _), double => isFalse (fun h => type.noConfusion h)
| (pair _ _), x86_80 => isFalse (fun h => type.noConfusion h)
| (pair _ _), (vec _ _) => isFalse (fun h => type.noConfusion h)
| (pair _ _), (fn _ _) => isFalse (fun h => type.noConfusion h)
| (fn _ _), (bv _) => isFalse (fun h => type.noConfusion h)
| (fn _ _), bit => isFalse (fun h => type.noConfusion h)
| (fn _ _), float => isFalse (fun h => type.noConfusion h)
| (fn _ _), double => isFalse (fun h => type.noConfusion h)
| (fn _ _), x86_80 => isFalse (fun h => type.noConfusion h)
| (fn _ _), (vec _ _) => isFalse (fun h => type.noConfusion h)
| (fn _ _), (pair _ _) => isFalse (fun h => type.noConfusion h)

instance decidable_eq_type : DecidableEq type := -- by tactic.mk_dec_eq_instance
  type.hasDecEq

end type

end mc_semantics


------------------------------------------------------------------------
-- X86

namespace x86

open mc_semantics
open mc_semantics.type

------------------------------------------------------------------------
-- type

-- Denotes the type of a register.
inductive gpreg_type : Type
| reg8l : gpreg_type
| reg8h : gpreg_type
| reg16 : gpreg_type
| reg32 : gpreg_type
| reg64 : gpreg_type

namespace gpreg_type

@[reducible]
def width : gpreg_type → Nat
| reg8l  => 8
| reg8h  => 8
| reg16 => 16
| reg32 => 32
| reg64 => 64

end gpreg_type

inductive Reg64
| rax : Reg64
| rcx : Reg64
| rdx : Reg64
| rbx : Reg64
| rsp : Reg64
| rbp : Reg64
| rsi : Reg64
| rdi : Reg64
| r8  : Reg64
| r9  : Reg64
| r10 : Reg64
| r11 : Reg64
| r12 : Reg64
| r13 : Reg64
| r14 : Reg64
| r15 : Reg64

-- Type for concrete x86 registers
inductive concrete_reg : type → Type
| gpreg   (idx:Fin 16) (tp:gpreg_type) : concrete_reg (bv (tp.width))
| flagreg (idx:Fin 32) : concrete_reg bit


-- Type for x86 registers
inductive reg (tp:type) : Type
| concrete  (c:concrete_reg tp) : reg
| arg {} (idx:arg_index) : reg

namespace reg

protected def gpreg_prefix (x:Fin 16) : String :=
  match x.val with
  | 0 => "a"
  | v => "r" ++ v.repr


protected def r8l_names : List String :=
  [ "al",   "cl",   "dl",   "bl"
  , "spl",  "bpl",  "sil",  "dil"
  , "r8b" , "r9b" , "r10b", "r11b"
  , "r12b", "r13b", "r14b", "r15b"
  ]

protected def r8h_names : List String :=
  [ "ah",   "ch",   "dh",   "bh"
  , "sph_undefined",  "bph_undefined",  "sih_undefined",  "dih_undefined"
  , "r8h_undefined" , "r9h_undefined" , "r10h_undefined", "r11h_undefined"
  , "r12h_undefined", "r13h_undefined", "r14h_undefined", "r15h_undefined"
  ]

protected def r16_names : List String :=
  [ "ax",   "cx",   "dx", "bx"
  , "sp",   "bp",   "si", "di"
  , "r8w" , "r9w" , "r10w", "r11w"
  , "r12w", "r13w", "r14w", "r15w"
  ]

protected def r32_names : List String :=
  [ "eax",  "ecx",  "edx",  "ebx"
  , "esp",  "ebp",  "esi",  "edi"
  , "r8d" , "r9d" , "r10d", "r11d"
  , "r12d", "r13d", "r14d", "r15d"
  ]

protected def r64_names : List String :=
  [ "rax", "rcx", "rdx", "rbx"
  , "rsp", "rbp", "rsi", "rdi"
  , "r8" , "r9" , "r10", "r11"
  , "r12", "r13", "r14", "r15"
  ]

protected def flag_names : List String :=
  [ "cf", "RESERVED_1", "pf",  "RESERVED_3", "af",    "RESERVED_5", "zf", "sf"
  , "tf", "if",         "df",  "of",         "iopl1", "iopl2",      "nt", "RESERVED_15"
  , "rf", "vm",         "ac",  "vif",        "vip",   "id"
  ]

end reg

namespace concrete_reg

protected
def repr : ∀{tp:type}, concrete_reg tp → String
| ._, (gpreg idx tp) => "$" ++
  (match tp with
  | gpreg_type.reg8l => List.get! idx.val reg.r8l_names
  | gpreg_type.reg8h => List.get! idx.val reg.r8h_names
  | gpreg_type.reg16 => List.get! idx.val reg.r16_names
  | gpreg_type.reg32 => List.get! idx.val reg.r32_names
  | gpreg_type.reg64 => List.get! idx.val reg.r64_names)
 
| ._, (flagreg idx) => "$" ++
   (match List.get? idx.val reg.flag_names with
   | (Option.some nm) => nm
   | Option.none      => "RESERVED_" ++ idx.val.repr)


end concrete_reg

namespace reg

protected
def repr : ∀{tp:type}, reg tp -> String
| _, (concrete r) => r.repr
| _, (arg idx)    => "arg" ++ idx.repr

end reg

------------------------------------------------------------------------
-- Addresses

-- Denotes an address to a value of a specific type.
inductive addr (tp:type) : Type
| arg {} (idx: arg_index) : addr

namespace addr

protected def repr {tp:type} : addr tp → String
| (arg idx) => idx.repr

end addr

------------------------------------------------------------------------
-- Primitive functions

section prim
-- local
infixr `.→`:30 := type.fn

-- This denotes primitive operations that are part of the semantics.
-- Unless otherwise specified primitive functions evaluate all their
-- arguments in left-to-right order before evaluating the function.
inductive prim : type → Type
-- `type` operations
-- `(eq tp)` returns `true` if two values are equal.
| eq (tp:type) : prim (tp .→ tp .→ bit)
-- `(neq tp)` returns `true` if two values are not equal.
| neq (tp:type) : prim (tp .→ tp .→ bit)
-- `(mux tp) c t f` evaluates to `t` when `c` is true and `f` otherwise.
-- This only evaluates `t` when `c` is true, and only evaluates `f` when
-- `c` is false.
| mux (tp:type) : prim (bit .→ tp .→ tp .→ tp)

-- Logical bit operations
-- `zero` is the zero bit
| bit_zero : prim bit
-- `one` is the one bit
| bit_one : prim bit
| bit_or : prim (bit .→ bit .→ bit)
| bit_and : prim (bit .→ bit .→ bit)
| bit_xor : prim (bit .→ bit .→ bit)

-- Bit vector operations
-- `bv_nat` constructs a bit vector from a natural number.
| bv_nat (w:Nat) : Nat → prim (bv w)
-- `(add i)` returns the sum of two i-bit numbers.
| add (i:Nat) : prim (bv i .→ bv i .→ bv i)
-- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
| adc (i:Nat) : prim (bv i .→ bv i .→ bit .→ bv i)
-- Unsigned add with carry overflow
| uadc_overflows (i:Nat) : prim (bv i .→ bv i .→ bit .→ bit)
-- Signed add with carry overflow
| sadc_overflows (i:Nat) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(sub i)` substracts two i-bit bitvectors.
| sub (i:Nat) : prim (bv i .→ bv i .→ bv i)
-- `(ssbb_overflows i)` true if signed sub overflows, the bit
-- is a borrow bit.
| ssbb_overflows (i:Nat) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(usbb_overflows i)` true if unsigned sub overflows,
-- the bit is a borrow bit.
| usbb_overflows (i:Nat) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(neg tp)` Two's Complement negation.
| neg (i:Nat) : prim (bv i .→ bv i)
-- `(mul i)` returns the product of two i-bit numbers.
| mul (i:Nat) : prim (bv i .→ bv i .→ bv i)
-- `(quotRem i) n d` returns a pair `(q,r)` where `q` is a `floor (n/d)`
-- and `r` is `n - d * floor (n/d)`.
-- `n` and `d` are treated as unsigned values.
-- If `d = 0` or `floor(n/d) >= 2^n`, then this triggers a #DE exception.
| quotRem (i:Nat) : prim (bv (2*i) .→ bv i .→ pair (bv i) (bv i))

-- `(squotRem i) n d` returns a pair `(q,r)` where `q` is a `trunc (n/d)`
-- and `r` is `n - d * trunc (n/d)`.  `trunc` always round to zero.
-- `n` and `d` are treated as signed values.
-- If `d = 0`, `trunc(n/d) >= 2^(n-1)` or `trunc(n/d) < -2^(n-1), then this
-- triggers a #DE exception when evaluated.
| squotRem (i:Nat) : prim (bv (2*i) .→ bv i .→ pair (bv i) (bv i))

| ule (i:Nat) : prim (bv i .→ bv i .→ bit)
| ult (i:Nat) : prim (bv i .→ bv i .→ bit)

-- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
| slice (w:Nat) (u:Nat) (l:Nat) : prim (bv w .→ bv (u+1-l))
-- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
| sext  (i:Nat) (o:Nat) : prim (bv i .→ bv o)
-- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
| uext  (i:Nat) (o:Nat) : prim (bv i .→ bv o)
-- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
| trunc (i:Nat) (o:Nat) : prim (bv i .→ bv o)
-- `(cat i) x y` returns the bitvector `uext i (2*i) x << i | uext _ (2*i) y`
| cat (i:Nat) : prim (bv i .→ bv i .→ bv (2*i))
-- Return the most-significant bit in the bitvector.
| msb (i:Nat) : prim (bv i .→ bit)

| bv_and (i:Nat) : prim (bv i .→ bv i .→ bv i)
| bv_or  (i:Nat) : prim (bv i .→ bv i .→ bv i)
| bv_xor (i:Nat) : prim (bv i .→ bv i .→ bv i)
-- Complement bits
| bv_complement (i:Nat) : prim (bv i .→ bv i)

--- `(shl i) x y` shifts the bits in `x` to the left by
--- `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in from the left are all zero.
| shl (i:Nat) : prim (bv i .→ bv 8 .→ bv i)
--- `(shl_carry w) c b i` returns the `i`th bit
--- in the bitvector [c]++b where `i` is treated as an unsigned
--- number with `0` as the most-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `[c] ++ b` (i.e., i >= w+1),
-- the the result is false.
| shl_carry (w:Nat) : prim (bit .→ bv w .→ bv 8 .→ bit)
--- `(shr i) x y` shifts the bits in `x` to the right by
--- `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in from the right are all zero.
| shr (i:Nat) : prim (bv i .→ bv 8 .→ bv i)
--- `(shr_carry w) b c i` returns the `i`th bit
--- in the bitvector b++[c] where `i` is treated as an unsigned
--- number with `0` as the least-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
-- the the result is false.
| shr_carry (w:Nat) : prim (bv w .→ bit .→ bv 8 .→ bit)
--- `(sar i) x y` arithmetically shifts the bits in `x` to
--- the left by `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in all match the most-significant bit in y.
| sar (i:Nat) : prim (bv i .→ bv 8 .→ bv i)
--- `(sar_carry w) b c i` returns the `i`th bit
--- in the bitvector b++[c] where `i` is treated as an unsigned
--- number with `0` as the least-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
-- the the result is equal to the most-signfiicant bit.
| sar_carry (w:Nat) : prim (bv w .→ bit .→ bv 8 .→ bit)

| even_parity (i:Nat) : prim (bv i .→ bit)
-- `(bsf i)` returns the index of least-significant bit that is 1.
| bsf   (i:Nat) : prim (bv i .→ bv i)
-- `(bsr i)` returns the index of most-significant bit that is 1.
| bsr   (i:Nat) : prim (bv i .→ bv i)
-- `(bswap i)` reverses the bytes in the bitvector.
| bswap (i:Nat) : prim (bv i .→ bv i)
-- `(btc w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is complemented.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| btc (w:one_of [16,32,64]) (j:Nat) : prim (bv w .→ bv j .→ bv w)
-- `(btr w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is cleared.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| btr (w:one_of [16,32,64]) (j:Nat) : prim (bv w .→ bv j .→ bv w)
-- `(bts w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is set.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| bts (w:one_of [16,32,64]) (j:Nat) : prim (bv w .→ bv j .→ bv w)

-- Floating point operations

-- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
| bv_to_x86_80  (w : one_of [16,32]) : prim (bv w .→ x86_80)
-- `float_to_x86_80` converts a float to an extended precision number (lossless)
| float_to_x86_80  : prim (float .→ x86_80)
-- `double_to_x86_80` converts a double to an extended precision number (lossless)
| double_to_x86_80 : prim (double .→ x86_80)
-- `x87_fadd` adds two extended precision values using the flags in the x87 register.
| x87_fadd : prim (x86_80 .→ x86_80 .→ x86_80)

-- Pairs

-- Return first element of a pair.
| pair_fst (x y : type) : prim (pair x y .→ x)
-- Return second element of a pair.
| pair_snd (x y : type) : prim (pair x y .→ y)

--- Denotes an immediate value appearing in the instruction.
inductive imm : type → Type
| arg (idx:arg_index) {tp:type} : imm tp


-- This is an expression that computes a value with some type given by
-- the parameter.
--
-- Note that our expression syntax has a constructor for "undef", this does not
-- denote a particular value, but means the processor may choose a different value
-- each time it needs to evaluate this expression.
--
-- This undef parameter is mainly used in assigning flags.
inductive expression : type → Type
-- Create a expression from a primitive
| primitive {rtp:type} (o:prim rtp) : expression rtp
-- `bv_bit_reg_reg wr wi r ri` treats `ri` as an unsigned number, lets `i = ri mod wr`, and
-- denotes the value in the `i`th bit of `r` with `0` the least-significant bit.
| bit_test {wr wi:Nat} (r : expression (bv wr)) (idx : expression (bv wi)) : expression bit
-- `mulc m x` denotes the value `m * x`.
| mulc (m : Nat) (x : expression (bv 64)) : expression (bv 64)
-- `quotc m x` denotes the value `x / m`.
| quotc (m : Nat) (x : expression (bv 64)) : expression (bv 64)
-- Denotes some value
| undef (rtp:type) : expression rtp
-- Apply a function to an argument.
| app {rtp:type} {tp:type} (f : expression (type.fn tp rtp)) (a : expression tp) : expression rtp
-- Get the value of the expression associated with the register.
| get_reg {tp:type} (r:concrete_reg tp) : expression tp
-- Read the address
| read (tp:type) (a : expression (bv 64)) : expression tp
-- Denotes the current value of a register as identified by an offset relative to the current stack top value.
| streg (idx : Fin 8) : expression x86_80
-- Denotes the value of a local variable at the given index.
| get_local (idx:Nat) (tp:type) : expression tp
-- Denotes the value of an argument that should be an immediate encoded in the machine code.
| imm_arg (idx:arg_index) (tp:type) : expression tp
-- Denotes the value of an argument that should be a memory address
-- that has been computed by the disassembler.
| addr_arg (idx:arg_index) : expression (bv 64)
-- Denotes an argument that may be either a register or address.
-- If a register, assigning to this will update current value stored in a
-- register.  If a memory address, this will read to the current address stored in memory.
-- An argument that may be either a register or address.
| read_arg (idx:arg_index) (tp:type) : expression tp

end prim

--namespace prim
--
-- def pp : ∀{tp:type}, prim tp → String
-- | ._ (add i) => "add " ++ i.pp
-- | ._ (adc i) => "adc " ++ i.pp
-- | ._ (mul i) => "mul " ++ i.pp
-- | ._ (quot i) => "quot " ++ i.pp
-- | ._ (rem i) => "rem " ++ i.pp
-- | ._ (squot i) => "squot " ++ i.pp
-- | ._ (srem i) => "srem " ++ i.pp
-- | ._ (slice w u l) => "slice " ++ w.pp ++ " " ++ u.pp ++ " " ++ l.pp
-- | ._ (sext i o) => "sext " ++ i.pp ++ " " ++ o.pp
-- | ._ (uext i o) => "uext " ++ i.pp ++ " " ++ o.pp
-- | ._ (trunc i o) => "trunc " ++ i.pp ++ " " ++ o.pp
-- | ._ (bsf i) => "bsf " ++ i.pp
-- | ._ (bsr i) => "bsr " ++ i.pp
-- | ._ (bswap i) => "bswap " ++ i.pp
-- | ._ bit_zero => sexp.app "bit" ["0"]
-- | ._ bit_one  => sexp.app "bit" ["1"]
-- | ._ (eq tp) => "eq " ++ tp.pp
-- | ._ (neq tp) => "neq " ++ tp.pp
-- | ._ (neg tp) => "neg " ++ tp.pp
-- | ._ x87_fadd => "x87_fadd"
-- | ._ float_to_x86_80 => "float_to_x86_80"
-- | ._ double_to_x86_80 => "double_to_X86_80"
-- | ._ (bv_to_x86_80 w) => "sext " ++ w.pp
-- | ._ (bv_nat w n) => sexp.app "bv_nat" [w.pp, n.pp]
-- | ._ (sub i) => "sub " ++ i.pp
-- | ._ (ssbb_overflows i) => "ssbb_overflows " ++ i.pp
-- | ._ (usbb_overflows i) => "usbb_overflows " ++ i.pp
-- | ._ (uadc_overflows i) => "uadc_overflows " ++ i.pp
-- | ._ (sadc_overflows i) => "sadc_overflows " ++ i.pp
-- | ._ (and i) => "and " ++ i.pp
-- | ._ (or  i) => "or "  ++ i.pp
-- | ._ (xor i) => "xor " ++ i.pp
-- | ._ (shl i) => "shl " ++ i.pp
-- | ._ (shr i) => "shr " ++ i.pp
-- | ._ (sar i) => "sar " ++ i.pp
-- | ._ (bv_bit i) => "bv_bit " ++ i.pp
-- | ._ (complement i) => "complement " ++ i.pp
-- | ._ (cat i) => "cat " ++ i.pp
-- | ._ (msb i) => "msb " ++ i.pp
-- | ._ (even_parity i) => "even_parity " ++ i.pp
-- | ._ bit_or  => "bit_or"
-- | ._ bit_and => "bit_and"
-- | ._ bit_xor => "bit_xor"
-- | ._ (ule i) => "ule " ++ i.pp
-- | ._ (ult i) => "ult " ++ i.pp
--
-- end prim

namespace expression

-- local notation Nat := nat_expr

def of_addr : ∀{tp:type}, addr tp → expression (bv 64)
| tp, (@addr.arg _ i) => expression.addr_arg i

instance prim_is_expr (rtp:type) : HasCoe (prim rtp) (expression rtp) := ⟨expression.primitive⟩

instance (a:type) (f:type) : HasCoeToFun (expression (type.fn a f)) :=
{ F := fun _ => ∀(y:expression a), expression f
, coe := app
}

def add : ∀{w:Nat}, expression (bv w) → expression (bv w) → expression (bv w)
--| ._ (primitive (prim.bv_nat ._ n)) (primitive (prim.bv_nat w m)) => prim.bv_nat w (n + m)
| i, x, y => prim.add i x y

def sub : ∀{w:Nat}, expression (bv w) → expression (bv w) → expression (bv w)
--| ._ (primitive (prim.bv_nat ._ n)) (primitive (prim.bv_nat w m)) => prim.bv_nat w (n - m)
| i, x, y => prim.sub i x y

def neg : ∀{w:Nat}, expression (bv w) → expression (bv w)
  | _, x => app (primitive (prim.neg _)) x

instance (w:Nat) : HasZero (expression (bv w)) := ⟨prim.bv_nat w 0⟩
instance (w:Nat) : HasOne  (expression (bv w)) := ⟨prim.bv_nat w 1⟩
instance (w:Nat) : HasAdd  (expression (bv w)) := ⟨add⟩
instance (w:Nat) : HasSub  (expression (bv w)) := ⟨sub⟩
instance (w:Nat) : HasNeg  (expression (bv w)) := ⟨neg⟩

def adc         {w:Nat} (x y : expression (bv w)) (b : expression bit) : expression (bv w) := prim.adc   w x y b
def bswap       {w:Nat} (v : expression (bv w))                        : expression (bv w) := prim.bswap w v
def bit_or            (x y : expression bit)                         : expression bit    := prim.bit_or  x y
def bit_and           (x y : expression bit)                         : expression bit    := prim.bit_and x y
def bit_xor           (x y : expression bit)                         : expression bit    := prim.bit_xor x y
def bv_nat (w:Nat) (x : Nat) : expression (bv w) := prim.bv_nat w x

def read_addr {tp:type} : addr tp → expression tp
| (addr.arg idx) => expression.read_arg idx tp

def of_reg {tp:type} : reg tp → expression tp
| (reg.concrete r) => expression.get_reg r
| (reg.arg a) => expression.read_arg a tp

instance addr_is_expression (tp:type) : HasCoe (addr tp) (expression tp) :=
⟨ expression.read_addr ⟩



instance type_is_sort     : HasCoeToSort type := ⟨Type, expression⟩
instance all_reg_is_expression : has_coe1 reg expression := ⟨fun _ => expression.of_reg⟩

end expression

protected
def expression.imm : ∀{tp:type}, imm tp → expression tp
| ._, (@imm.arg i tp) => expression.imm_arg i tp

instance expression.imm_is_expression (tp:type) : HasCoe (imm tp) (expression tp) := ⟨expression.imm⟩

-- Operations on expressions

def slice {w:Nat} (x:expression (bv w)) (u:Nat) (l:Nat)
: expression (bv (u+1-l)) := prim.slice w u l x

def trunc {w:Nat} (x: bv w) (o:Nat) : bv o := prim.trunc w o x

def bsf {w:Nat} (x: bv w) : bv w := prim.bsf w x

def bsr {w:Nat} (x: bv w) : bv w := prim.bsr w x

def sext {w:Nat} (x: bv w) (o:Nat) : bv o := prim.sext w o x

def uext {w:Nat} (x: bv w) (o:Nat) : bv o := prim.uext w o x

def neq {tp:type} (x y : tp) : bit := prim.neq tp x y

def eq {tp:type} (x y : tp) : bit := prim.eq tp x y

def bit_one  : bit := prim.bit_one
def bit_zero : bit := prim.bit_zero

instance bv_has_mul (w:Nat) : HasMul (bv w) := ⟨fun x y => prim.mul w x y⟩

-- Add two 80-bit numbers using the current x87 floating point control.
def x87_fadd (x y : x86_80) : x86_80 := prim.x87_fadd x y

instance float_extends_to_80  : HasCoe float  x86_80 := ⟨prim.float_to_x86_80⟩

instance double_extends_to_80 : HasCoe double x86_80 := ⟨prim.double_to_x86_80⟩

-- These are lossless conversions.
instance bv_to_x86_80  (w:one_of [16,32]) : HasCoe (bv w) x86_80 := ⟨prim.bv_to_x86_80 w⟩

------------------------------------------------------------------------
-- Left-hand sides for assignments.

--- Expressions that may appear on the left-hand side of an assignment.
inductive lhs : type → Type
| set_reg {tp:type} (r:concrete_reg tp) : lhs tp
-- Write to the address denoted by an expression.
| write_addr (a:expression (bv 64)) (tp:type) : lhs tp
-- Denotes an argument that may be either a register or address.
-- If a register, assigning to this will update current value stored in a
-- register.  If a memory address, this will write to the current address stored in memory.
| write_arg (idx:arg_index) (tp:type) : lhs tp
-- ST reg with the offset relative to the current stack top value.
| streg (idx : Fin 8) : lhs x86_80

namespace lhs

def of_addr {tp:type} : addr tp → lhs tp
| (addr.arg idx) => lhs.write_arg idx tp

def of_reg {tp:type} : reg tp → lhs tp
| (reg.concrete r) => lhs.set_reg r
| (reg.arg idx) => lhs.write_arg idx tp

end lhs


namespace expression
def of_lhs : ∀{tp:type}, lhs tp → expression tp
| ._, (lhs.set_reg r) => expression.get_reg r
| ._, (lhs.write_addr a tp) => expression.read tp a
| ._, (lhs.write_arg idx tp) => expression.read_arg idx tp
| ._, (lhs.streg idx) => expression.streg idx

instance all_lhs_is_expression : has_coe1 lhs expression := ⟨fun _ => expression.of_lhs⟩

instance lhs_is_expression (tp:type) : HasCoe (lhs tp) (expression tp) := ⟨expression.of_lhs⟩

end expression


section

def reg8l (i:Fin 16) : lhs (bv 8) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg8l
def reg8h (i:Fin 16) : lhs (bv 8) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg8h

def al  := reg8l 0
def cl  := reg8l 1
def dl  := reg8l 2
def bl  := reg8l 3
def spl := reg8l 4
def bpl := reg8l 5
def sil := reg8l 6
def dil := reg8l 7
def ah  := reg8h 0

def reg16 (i:Fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg16

def ax := reg16 0
def cx := reg16 1
def dx := reg16 2
def bx := reg16 3

def reg32 (i:Fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg32

def eax := reg32 0
def ecx := reg32 1
def edx := reg32 2
def ebx := reg32 3

def reg64 (i:Fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg64

def rax := reg64 0
def rcx := reg64 1
def rdx := reg64 2
def rbx := reg64 3
def rsp := reg64 4
def rbp := reg64 5
def rsi := reg64 6
def rdi := reg64 7
def r8  := reg64 8
def r9  := reg64 9
def r10 := reg64 10
def r11 := reg64 11
def r12 := reg64 12
def r13 := reg64 13
def r14 := reg64 14
def r15 := reg64 15

def flagreg (i:Fin 32) := lhs.set_reg $ concrete_reg.flagreg i

def cf  := flagreg  0
def pf  := flagreg  2
def af  := flagreg  4
def zf  := flagreg  6
def sf  := flagreg  7
def tf  := flagreg  8
def if' := flagreg  9
def df  := flagreg 10
def of  := flagreg 11

def st0 : lhs x86_80 := lhs.streg 0

end

------------------------------------------------------------------------
-- event

-- These are a type of action that may have side effects, but do
-- not return values.
inductive event
| syscall : event
| unsupported (msg:String) : event
| pop_x87_register_stack : event
| call (addr: bv 64) : event
| jmp  (addr: bv 64) : event
| branch : expression bit → bv 64 → event
| hlt : event
| xchg {w : Nat} (addr1: bv w) (addr2: bv w) : event
| cpuid : event

------------------------------------------------------------------------
-- action

-- Denotes updates to program state from register.
inductive action
--- Set a left-hand side to an undefined value.
| set            {tp:type} (l:lhs tp) (v:expression tp) : action
-- Conditionally set the lhs
| set_cond       {tp:type} (l:lhs tp) (c: expression bit) (v:expression tp) : action
-- Set the lhs but raise an exception when the lhs does not have proper alignment
-- TODO: Document what precisely is meant by "exception" when alignment is not
-- respected.
| set_aligned    {tp:type} (l:lhs tp) (v:expression tp) (alignment:Nat) : action
-- Define a local variable for an expression.
| local_def {tp:type} (idx:Nat) (v:expression tp) : action
| event (e:event) : action

--- Mark an lhs as undefined
def action.set_undef {tp:type} (l:lhs tp) : action := action.set l (expression.undef tp)

--- Conditionally mark an lhs as undefined
def action.set_undef_cond {tp:type} (l:lhs tp) (c: expression bit) : action :=
  action.set_cond l c (expression.undef tp)

------------------------------------------------------------------------
-- binding

inductive binding
| reg  : type → binding
| addr : type → binding
| imm  : type → binding
| lhs  : type → binding
| expression : type → binding

------------------------------------------------------------------------
-- context

structure context :=
(bindings : List binding)

def context.length (c:context) : arg_index := c.bindings.length

def context.add (b:binding) (ctx:context) : context :=
{ bindings := b :: ctx.bindings }

-- instance : HasInsert binding context := ⟨context.add⟩
def context.insert := context.add

instance : HasEmptyc context :=
⟨{bindings := []}⟩

------------------------------------------------------------------------
-- Patterns

structure pattern :=
(context : context)
(actions : List action)

------------------------------------------------------------------------
-- instruction

structure instruction :=
(mnemonic:String)
(patterns:List pattern)

------------------------------------------------------------------------
-- is_bound_var

-- Class for types that may be used as arguments in defining semantics.
class is_bound_var (tp:Type) :=
(to_binding{} : binding)
(mk_arg{} : arg_index → tp)

-- instance one_of_is_bound_var (range:List Nat) : is_bound_var (one_of range) :=
-- { to_binding := binding.one_of range
-- , mk_arg := one_of.var
-- }

instance reg_is_bound_var (tp:type) : is_bound_var (reg tp) :=
{ to_binding := binding.reg tp
, mk_arg := fun i => reg.arg i
}

instance addr_is_bound_var (tp:type) : is_bound_var (addr tp) :=
{ to_binding := binding.addr tp
, mk_arg := fun i => addr.arg i
}

instance imm_is_bound_var (tp:type) : is_bound_var (imm tp) :=
{ to_binding := binding.imm tp
, mk_arg := fun i => imm.arg i
}


instance lhs_is_bound_var (tp:type) : is_bound_var (lhs tp) :=
{ to_binding := binding.lhs tp
, mk_arg := fun i => lhs.write_arg i tp
}

instance expression_is_bound_var (tp:type) : is_bound_var (expression tp) :=
{ to_binding := binding.expression tp
, mk_arg := fun i => expression.read_arg i tp
}

------------------------------------------------------------------------
-- semantics

structure semantics_state : Type :=
-- Actions seen so far in reverse order.
(actions : List action)
-- Number of local constants to use.
(local_variable_count : Nat)

namespace semantics_state

def init : semantics_state :=
{ actions := []
, local_variable_count := 0
}

end semantics_state

structure semantics (α:Type) :=
(monad : StateM semantics_state α)

instance : Monad semantics :=
{ pure := fun _ x => { monad := pure x }
, bind := fun _ _ m h => { monad := m.monad >>= fun v => (h v).monad }
, map := fun _ _ f m => { monad := f <$> m.monad }
}

namespace semantics

--- Get the index to use for the next local variable.
protected
def next_local_index : semantics Nat :=
  { monad := do
      s ← get;
      set { local_variable_count := s.local_variable_count + 1, .. s };
      pure s.local_variable_count
  }

-- --- Get the index to use for the next local variable.
-- protected
-- def next_local_index : semantics Nat :=
--   { monad := do
--       s ← get,
--       set {s with local_variable_count := s.local_variable_count + 1 },
--       pure s.local_variable_count
--   }

--- Add an action to the List of actions.
protected
def add_action (e:action) : semantics Unit :=
  { monad := modify (fun s => { s with actions := e :: s.actions}) }

def record_event (e:event) : semantics Unit :=
  semantics.add_action (action.event e)

-- Record that some code path is unsupported.
def unsupported (msg:String) := record_event (event.unsupported msg)

--- Set the expression of the left-hand side to the expression.
def set {tp:type} (l:lhs tp) (v:expression tp) : semantics Unit :=
  semantics.add_action (action.set l v)

--- Set the expression of the left-hand side to the expression and respect alignment.
def set_aligned {tp:type} (l:lhs tp) (v:expression tp) (a:Nat): semantics Unit :=
  semantics.add_action (action.set_aligned l v a)

def set_cond {tp:type} (l:lhs tp) (c: expression bit) (v:expression tp) : semantics Unit :=
  semantics.add_action (action.set_cond l c v)

--- Evaluate the given expression and return a local expression that will not mutate.
def eval {tp : type} (v:expression tp) : semantics (expression tp) := do
  idx ← semantics.next_local_index;
  semantics.add_action (action.local_def idx v);
  pure (expression.get_local idx tp)

protected
def run (m:semantics Unit) : List action := do
  (m.monad.run semantics_state.init).snd.actions.reverse

end semantics

------------------------------------------------------------------------
-- pattern_def

-- Class for functions of form fun ... -> semantics Unit
--
-- This is used to define patterns with lambdas to bind arguments.  The context variable
-- is needed so that we can infer how many variables have been bound outside of the
-- current context.
class pattern_def (ctx : context) (tp:Type) :=
{ define{} : tp → List pattern }

instance semantics_is_pattern_def (ctx : context)
: pattern_def ctx (semantics Unit) := { define := fun m =>
    [ { context := ctx
      , actions := semantics.run m
      } 
    ]
  }

instance pi_is_pattern_def
  (tp:Type)
  [is_bound_var tp]
  (ctx:context)
  (β:tp → Type)
  [pattern_def (context.insert (is_bound_var.to_binding tp) ctx) (β (is_bound_var.mk_arg ctx.length))]
: pattern_def ctx (∀(w: tp), β w) :=
{ define := fun f => do
    pattern_def.define (context.insert (is_bound_var.to_binding tp) ctx) (f (is_bound_var.mk_arg ctx.length))
}

class one_of_pattern_def (ctx : context) (ls : List Nat) (sls : List Nat) -- (pf : isSuffixOf sls ls)
                         (tpc: one_of ls -> Type) :=
      { list_define : (forall (w : one_of ls), tpc w) -> List pattern }

instance nil_one_of_pattern_def
  (ctx : context) (ls : List Nat) (tpc: one_of ls -> Type) 
: one_of_pattern_def ctx ls [] tpc :=
{ list_define := fun _ => [] }

instance cons_one_of_pattern_def
  (ctx : context) (ls : List Nat) (v : Nat) (sls : List Nat) (tpc: one_of ls -> Type)
  [ h : one_of_pattern_def ctx ls sls tpc ]
  [ pattern_def ctx (tpc (one_of.elem v)) ]
: one_of_pattern_def ctx ls (v :: sls) tpc :=
{ list_define := fun f => 
              -- we reverse at the end, so this ensures order is preserved
              List.append (@one_of_pattern_def.list_define ctx ls sls tpc h f)
                          (pattern_def.define ctx (f (one_of.elem v)))
                          
}

instance pi_one_of_is_pattern_def
  (ls : List Nat)
  (ctx:context)
  (β:one_of ls → Type)
  [ h: one_of_pattern_def ctx ls ls β ]
: pattern_def ctx (∀(w: one_of ls), β w) := 
{ define := @one_of_pattern_def.list_define ctx ls ls β h }

-- Contains a List of patten matches defined using a monadic syntax.
-- @[derive Monad]
def pattern_list : Type → Type := StateM (List pattern)

instance pattern_list_is_monad : Monad pattern_list
  := inferInstanceAs (Monad (StateM (List pattern)))

instance pattern_list_is_monad_state : MonadState (List pattern) pattern_list
  := inferInstanceAs (MonadState (List pattern) (StateM (List pattern)))

-- instance pattern_list_is_monad : Monad pattern_list :=
-- begin
--   simp [pattern_list],
--   apply_instance,
-- end

-- Record pattern in current instruction
def mk_pattern {α:Type} [h : pattern_def ∅ α] (x:α) : pattern_list Unit := do
  modify (List.append (pattern_def.define ∅ x))


------------------------------------------------------------------------
-- definst

-- Create an instruction definition from mnemonic name and likst of patterns.
def definst (mnem:String) (pat: pattern_list Unit) : instruction :=
{ mnemonic := mnem
, patterns := (pat.run []).snd.reverse
}

end x86
