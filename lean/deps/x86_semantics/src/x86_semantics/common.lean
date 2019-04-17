/-
This module defines the core datatypes used to represent x86 instruction semantics.
-/
import galois.category.coe1
import galois.sexpr

namespace mc_semantics

------------------------------------------------------------------------
-- arg_index

/- This denotes the index of a variable in a context.

It is equivant to a deBrujin level.
-/
@[reducible]
def arg_index := nat

------------------------------------------------------------------------
-- nat_expr

inductive nat_expr : Type
| lit : nat → nat_expr
| var : arg_index → nat_expr
| add : nat_expr → nat_expr → nat_expr
| sub : nat_expr → nat_expr → nat_expr
| mul : nat_expr → nat_expr → nat_expr
-- div x y is floor (x / y)
| div : nat_expr → nat_expr → nat_expr

namespace nat_expr

protected def zero : nat_expr := lit 0

protected def one : nat_expr := lit 1

protected def do_add : nat_expr → nat_expr → nat_expr
| (lit x) (lit y) := lit (x+y)
| x y := add x y

protected def do_sub : nat_expr → nat_expr → nat_expr
| (lit x) (lit y) := lit (x-y)
| x y := sub x y

protected def do_mul : nat_expr → nat_expr → nat_expr
| (lit x) (lit y) := lit (x*y)
| x y := mul x y

protected def do_div : nat_expr → nat_expr → nat_expr
| (lit x) (lit y) := lit (x/y)
| x y := div x y

instance : has_zero nat_expr := ⟨nat_expr.zero⟩
instance : has_one nat_expr := ⟨nat_expr.one⟩
instance : has_add nat_expr := ⟨nat_expr.do_add⟩
instance : has_sub nat_expr := ⟨nat_expr.do_sub⟩
instance : has_mul nat_expr := ⟨nat_expr.do_mul⟩
instance : has_div nat_expr := ⟨nat_expr.do_div⟩

instance nat_coe_nat_expr : has_coe ℕ nat_expr := ⟨λx, lit x⟩
instance decidable_eq_nat_expr : decidable_eq nat_expr := by tactic.mk_dec_eq_instance

def pp : nat_expr -> string
| (lit n) := repr n
| (var i) := "(var " ++ repr i ++ ")"
| (add e e') := "(add " ++ e.pp ++ " " ++ e'.pp ++ ")"
| (sub e e') := "(sub " ++ e.pp ++ " " ++ e'.pp ++ ")"
| (mul e e') := "(mul " ++ e.pp ++ " " ++ e'.pp ++ ")"
| (div e e') := "(div " ++ e.pp ++ " " ++ e'.pp ++ ")"

end nat_expr
------------------------------------------------------------------------
-- one_of

inductive one_of (l:list ℕ) : Type
| var{} : arg_index → one_of

namespace one_of

def to_nat_expr {l:list ℕ} : one_of l → nat_expr
| (one_of.var i) := nat_expr.var i

instance (l:list ℕ) : has_coe (one_of l) nat_expr :=
⟨ one_of.to_nat_expr ⟩

end one_of

------------------------------------------------------------------------
-- Type

inductive type
| bv (w:nat_expr) : type
| bit : type
| float  : type
| double : type
| x86_80 : type
| vec (w:nat_expr) (tp:type) : type
-- A pair with fields of the given type.
-- N.B. We use pairs rather than more general tuples for now, just for simplicity.
-- We do not need this currently, but have left it available in case it is needed soon.
| pair (x y : type) : type
-- A function from arg to res
| fn (arg:type) (res:type) : type

instance decidable_eq_type: decidable_eq type := by tactic.mk_dec_eq_instance

namespace type

protected
def pp' : Π(in_fun:bool), type → string
| _ (bv w) := "(bv " ++ w.pp ++ ")"
| _ bit    := "bit"
| _ float  := "float"
| _ double := "double"
| _ x86_80 := "x86_80"
| _ (vec w tp) := "(vec " ++ w.pp ++ " " ++ tp.pp' ff ++ ")"
| _ (pair tp tp') := "(pair " ++ tp.pp' ff ++ " " ++ tp'.pp' ff ++ ")"
| in_fun (fn a r) :=
  if in_fun then
     a.pp' ff ++ " " ++ r.pp' tt
  else
     "(fun " ++ a.pp' ff ++ " " ++ r.pp' tt ++ ")"

protected
def pp : type → string := type.pp' ff

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
def width' : gpreg_type → nat
| reg8l  := 8
| reg8h  := 8
| reg16 := 16
| reg32 := 32
| reg64 := 64

@[reducible]
def width : gpreg_type → nat_expr
| reg8l  := 8
| reg8h  := 8
| reg16 := 16
| reg32 := 32
| reg64 := 64

end gpreg_type

-- Type for concrete x86 registers
inductive concrete_reg : type → Type
| gpreg   (idx:fin 16) (tp:gpreg_type) : concrete_reg (bv (tp.width))
| flagreg (idx:fin 32) : concrete_reg bit

-- Type for x86 registers
inductive reg (tp:type) : Type
| concrete  (c:concrete_reg tp) : reg
| arg {} (idx:arg_index) : reg

namespace reg

protected def gpreg_prefix (x:fin 16) : string :=
  match x.val with
  | 0 := "a"
  | v := "r" ++ v.repr
  end

protected def r8l_names : list string :=
  [ "al",   "cl",   "dl",   "bl"
  , "spl",  "bpl",  "sil",  "dil"
  , "r8b" , "r9b" , "r10b", "r11b"
  , "r12b", "r13b", "r14b", "r15b"
  ]

protected def r8h_names : list string :=
  [ "ah",   "ch",   "dh",   "bh"
  , "sph_undefined",  "bph_undefined",  "sih_undefined",  "dih_undefined"
  , "r8h_undefined" , "r9h_undefined" , "r10h_undefined", "r11h_undefined"
  , "r12h_undefined", "r13h_undefined", "r14h_undefined", "r15h_undefined"
  ]

protected def r16_names : list string :=
  [ "ax",   "cx",   "dx", "bx"
  , "sp",   "bp",   "si", "di"
  , "r8w" , "r9w" , "r10w", "r11w"
  , "r12w", "r13w", "r14w", "r15w"
  ]

protected def r32_names : list string :=
  [ "eax",  "ecx",  "edx",  "ebx"
  , "esp",  "ebp",  "esi",  "edi"
  , "r8d" , "r9d" , "r10d", "r11d"
  , "r12d", "r13d", "r14d", "r15d"
  ]

protected def r64_names : list string :=
  [ "rax", "rcx", "rdx", "rbx"
  , "rsp", "rbp", "rsi", "rdi"
  , "r8" , "r9" , "r10", "r11"
  , "r12", "r13", "r14", "r15"
  ]

protected def flag_names : list string :=
  [ "cf", "RESERVED_1", "pf",  "RESERVED_3", "af",    "RESERVED_5", "zf", "sf"
  , "tf", "if",         "df",  "of",         "iopl1", "iopl2",      "nt", "RESERVED_15"
  , "rf", "vm",         "ac",  "vif",        "vip",   "id"
  ]

end reg

namespace concrete_reg

protected
def repr : Π{tp:type}, concrete_reg tp → string
| ._ (gpreg idx tp) := "$" ++
  match tp with
  | gpreg_type.reg8l := list.nth_le reg.r8l_names idx.val idx.is_lt
  | gpreg_type.reg8h := list.nth_le reg.r8h_names idx.val idx.is_lt
  | gpreg_type.reg16 := list.nth_le reg.r16_names idx.val idx.is_lt
  | gpreg_type.reg32 := list.nth_le reg.r32_names idx.val idx.is_lt
  | gpreg_type.reg64 := list.nth_le reg.r64_names idx.val idx.is_lt
  end
| ._ (flagreg idx) := "$" ++
   match list.nth reg.flag_names idx.val with
   | (option.some nm) := nm
   | option.none :=  "RESERVED_" ++ idx.val.repr
   end

end concrete_reg

namespace reg

protected
def repr : Π{tp:type}, reg tp -> string
| _ (concrete r) := r.repr
| _ (arg idx)    := "arg" ++ idx.repr

end reg

------------------------------------------------------------------------
-- Addresses

-- Denotes an address to a value of a specific type.
inductive addr (tp:type) : Type
| arg {} (idx: arg_index) : addr

namespace addr

protected def repr {tp:type} : addr tp → string
| (arg idx) := idx.repr

end addr

------------------------------------------------------------------------
-- Primitive functions

section prim
local infixr `.→`:30 := type.fn

local notation ℕ := nat_expr

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
| bv_nat (w:ℕ) : nat_expr → prim (bv w)
-- `(add i)` returns the sum of two i-bit numbers.
| add (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- `(adc i)` returns the sum of two i-bit numbers and a carry bit.
| adc (i:ℕ) : prim (bv i .→ bv i .→ bit .→ bv i)
-- Unsigned add with carry overflow
| uadc_overflows (i:ℕ) : prim (bv i .→ bv i .→ bit .→ bit)
-- Signed add with carry overflow
| sadc_overflows (i:ℕ) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(sub i)` substracts two i-bit bitvectors.
| sub (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- `(ssbb_overflows i)` true if signed sub overflows, the bit
-- is a borrow bit.
| ssbb_overflows (i:ℕ) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(usbb_overflows i)` true if unsigned sub overflows,
-- the bit is a borrow bit.
| usbb_overflows (i:ℕ) : prim (bv i .→ bv i .→ bit .→ bit)
-- `(neg tp)` Two's Complement negation.
| neg (i:ℕ) : prim (bv i .→ bv i)
-- `(mul i)` returns the product of two i-bit numbers.
| mul (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- `(quotRem i) n d` returns a pair `(q,r)` where `q` is a `floor (n/d)`
-- and `r` is `n - d * floor (n/d)`.
-- `n` and `d` are treated as unsigned values.
-- If `d = 0` or `floor(n/d) >= 2^n`, then this triggers a #DE exception.
| quotRem (i:ℕ) : prim (bv (2*i) .→ bv i .→ pair (bv i) (bv i))

-- `(squotRem i) n d` returns a pair `(q,r)` where `q` is a `trunc (n/d)`
-- and `r` is `n - d * trunc (n/d)`.  `trunc` always round to zero.
-- `n` and `d` are treated as signed values.
-- If `d = 0`, `trunc(n/d) >= 2^(n-1)` or `trunc(n/d) < -2^(n-1), then this
-- triggers a #DE exception when evaluated.
| squotRem (i:ℕ) : prim (bv (2*i) .→ bv i .→ pair (bv i) (bv i))

| ule (i:ℕ) : prim (bv i .→ bv i .→ bit)
| ult (i:ℕ) : prim (bv i .→ bv i .→ bit)

-- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
| slice (w:ℕ) (u:ℕ) (l:ℕ) : prim (bv w .→ bv (u+1-l))
-- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
| sext  (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
| uext  (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
| trunc (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(cat i) x y` returns the bitvector `uext i (2*i) x << i | uext _ (2*i) y`
| cat (i:ℕ) : prim (bv i .→ bv i .→ bv (2*i))
-- Return the most-significant bit in the bitvector.
| msb (i:ℕ) : prim (bv i .→ bit)

| bv_and (i:ℕ) : prim (bv i .→ bv i .→ bv i)
| bv_or  (i:ℕ) : prim (bv i .→ bv i .→ bv i)
| bv_xor (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- Complement bits
| bv_complement (i:ℕ) : prim (bv i .→ bv i)

--- `(shl i) x y` shifts the bits in `x` to the left by
--- `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in from the left are all zero.
| shl (i:ℕ) : prim (bv i .→ bv 8 .→ bv i)
--- `(shl_carry w) c b i` returns the `i`th bit
--- in the bitvector [c]++b where `i` is treated as an unsigned
--- number with `0` as the most-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `[c] ++ b` (i.e., i >= w+1),
-- the the result is false.
| shl_carry (w:ℕ) : prim (bit .→ bv w .→ bv 8 .→ bit)
--- `(shr i) x y` shifts the bits in `x` to the right by
--- `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in from the right are all zero.
| shr (i:ℕ) : prim (bv i .→ bv 8 .→ bv i)
--- `(shr_carry w) b c i` returns the `i`th bit
--- in the bitvector b++[c] where `i` is treated as an unsigned
--- number with `0` as the least-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
-- the the result is false.
| shr_carry (w:ℕ) : prim (bv w .→ bit .→ bv 8 .→ bit)
--- `(sar i) x y` arithmetically shifts the bits in `x` to
--- the left by `y` bits where `y` is treated as an unsigned integer.
--- The new bits shifted in all match the most-significant bit in y.
| sar (i:ℕ) : prim (bv i .→ bv 8 .→ bv i)
--- `(sar_carry w) b c i` returns the `i`th bit
--- in the bitvector b++[c] where `i` is treated as an unsigned
--- number with `0` as the least-significant bit.
-- e.g., If `i` is `0`, then this returns `c`.  If `i`
-- exceeds the number of bits in `b++[c]` (i.e., i >= w+1),
-- the the result is equal to the most-signfiicant bit.
| sar_carry (w:ℕ) : prim (bv w .→ bit .→ bv 8 .→ bit)

| even_parity (i:ℕ) : prim (bv i .→ bit)
-- `(bsf i)` returns the index of least-significant bit that is 1.
| bsf   (i:ℕ) : prim (bv i .→ bv i)
-- `(bsr i)` returns the index of most-significant bit that is 1.
| bsr   (i:ℕ) : prim (bv i .→ bv i)
-- `(bswap i)` reverses the bytes in the bitvector.
| bswap (i:ℕ) : prim (bv i .→ bv i)
-- `(btc w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is complemented.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| btc (w:one_of [16,32,64]) (j:ℕ) : prim (bv w .→ bv j .→ bv w)
-- `(btr w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is cleared.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| btr (w:one_of [16,32,64]) (j:ℕ) : prim (bv w .→ bv j .→ bv w)
-- `(bts w j) base idx` interprets base as bitvector and returns
-- a bitvector contains the same bits as `base` except the `i`th bit
-- (where 0 denotes the least-significant bit) is set.
-- The value `i` is `idx` as a unsigned integer modulo `w`.
| bts (w:one_of [16,32,64]) (j:ℕ) : prim (bv w .→ bv j .→ bv w)

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
| bit_test {wr wi:ℕ} (r : expression (bv wr)) (idx : expression (bv wi)) : expression bit
-- `mulc m x` denotes the value `m * x`.
| mulc (m : ℕ) (x : expression (bv 64)) : expression (bv 64)
-- `quotc m x` denotes the value `x / m`.
| quotc (m : ℕ) (x : expression (bv 64)) : expression (bv 64)
-- Denotes some value
| undef (rtp:type) : expression rtp
-- Apply a function to an argument.
| app {rtp:type} {tp:type} (f : expression (type.fn tp rtp)) (a : expression tp) : expression rtp
-- Get the value of the expression associated with the assignable expression.
| get_reg {tp:type} (r:concrete_reg tp) : expression tp
-- Read the address
| read (tp:type) (a : expression (bv 64)) : expression tp
-- Denotes the current value of a register as identified by an offset relative to the current stack top value.
| streg (idx : fin 8) : expression x86_80
-- Denotes the value of a local variable at the given index.
| get_local (idx:nat) (tp:type) : expression tp
-- Denotes the value of an argument that should be an immediate encoded in the machine code.
| imm_arg (idx:arg_index) (tp:type) : expression tp
-- Denotes the value of an argument that should be a memory address that has been computed by the disassembler.
| addr_arg (idx:arg_index) : expression (bv 64)
-- Denotes an argument that may be either a register or address.
-- If a register, assigning to this will update current value stored in a
-- register.  If a memory address, this will read to the current address stored in memory.
-- An argument that may be either a register or address.
| read_arg (idx:arg_index) (tp:type) : expression tp

end prim

--namespace prim
--
-- def pp : Π{tp:type}, prim tp → string
-- | ._ (add i) := "add " ++ i.pp
-- | ._ (adc i) := "adc " ++ i.pp
-- | ._ (mul i) := "mul " ++ i.pp
-- | ._ (quot i) := "quot " ++ i.pp
-- | ._ (rem i) := "rem " ++ i.pp
-- | ._ (squot i) := "squot " ++ i.pp
-- | ._ (srem i) := "srem " ++ i.pp
-- | ._ (slice w u l) := "slice " ++ w.pp ++ " " ++ u.pp ++ " " ++ l.pp
-- | ._ (sext i o) := "sext " ++ i.pp ++ " " ++ o.pp
-- | ._ (uext i o) := "uext " ++ i.pp ++ " " ++ o.pp
-- | ._ (trunc i o) := "trunc " ++ i.pp ++ " " ++ o.pp
-- | ._ (bsf i) := "bsf " ++ i.pp
-- | ._ (bsr i) := "bsr " ++ i.pp
-- | ._ (bswap i) := "bswap " ++ i.pp
-- | ._ bit_zero := sexp.app "bit" ["0"]
-- | ._ bit_one  := sexp.app "bit" ["1"]
-- | ._ (eq tp) := "eq " ++ tp.pp
-- | ._ (neq tp) := "neq " ++ tp.pp
-- | ._ (neg tp) := "neg " ++ tp.pp
-- | ._ x87_fadd := "x87_fadd"
-- | ._ float_to_x86_80 := "float_to_x86_80"
-- | ._ double_to_x86_80 := "double_to_X86_80"
-- | ._ (bv_to_x86_80 w) := "sext " ++ w.pp
-- | ._ (bv_nat w n) := sexp.app "bv_nat" [w.pp, n.pp]
-- | ._ (sub i) := "sub " ++ i.pp
-- | ._ (ssbb_overflows i) := "ssbb_overflows " ++ i.pp
-- | ._ (usbb_overflows i) := "usbb_overflows " ++ i.pp
-- | ._ (uadc_overflows i) := "uadc_overflows " ++ i.pp
-- | ._ (sadc_overflows i) := "sadc_overflows " ++ i.pp
-- | ._ (and i) := "and " ++ i.pp
-- | ._ (or  i) := "or "  ++ i.pp
-- | ._ (xor i) := "xor " ++ i.pp
-- | ._ (shl i) := "shl " ++ i.pp
-- | ._ (shr i) := "shr " ++ i.pp
-- | ._ (sar i) := "sar " ++ i.pp
-- | ._ (bv_bit i) := "bv_bit " ++ i.pp
-- | ._ (complement i) := "complement " ++ i.pp
-- | ._ (cat i) := "cat " ++ i.pp
-- | ._ (msb i) := "msb " ++ i.pp
-- | ._ (even_parity i) := "even_parity " ++ i.pp
-- | ._ bit_or  := "bit_or"
-- | ._ bit_and := "bit_and"
-- | ._ bit_xor := "bit_xor"
-- | ._ (ule i) := "ule " ++ i.pp
-- | ._ (ult i) := "ult " ++ i.pp
--
-- end prim

namespace expression

local notation ℕ := nat_expr

def of_addr : Π{tp:type}, addr tp → expression (bv 64)
| tp (@addr.arg _ i) := expression.addr_arg i

instance prim_is_expr (rtp:type) : has_coe (prim rtp) (expression rtp) := ⟨expression.primitive⟩

instance (a:type) (f:type) : has_coe_to_fun (expression (type.fn a f)) :=
{ F := λ_, Π(y:expression a), expression f
, coe := app
}

def add : Π{w:ℕ}, expression (bv w) → expression (bv w) → expression (bv w)
--| ._ (primitive (prim.bv_nat ._ n)) (primitive (prim.bv_nat w m)) := prim.bv_nat w (n + m)
| i x y := prim.add i x y

def sub : Π{w:ℕ}, expression (bv w) → expression (bv w) → expression (bv w)
--| ._ (primitive (prim.bv_nat ._ n)) (primitive (prim.bv_nat w m)) := prim.bv_nat w (n - m)
| i x y := prim.sub i x y

def neg : Π{w:ℕ}, expression (bv w) → expression (bv w)
  | _ x := app (primitive (prim.neg _)) x

instance (w:ℕ) : has_zero (expression (bv w)) := ⟨prim.bv_nat w 0⟩
instance (w:ℕ) : has_one  (expression (bv w)) := ⟨prim.bv_nat w 1⟩
instance (w:ℕ) : has_add  (expression (bv w)) := ⟨add⟩
instance (w:ℕ) : has_sub  (expression (bv w)) := ⟨sub⟩
instance (w:ℕ) : has_neg  (expression (bv w)) := ⟨neg⟩

def adc         {w:ℕ} (x y : expression (bv w)) (b : expression bit) : expression (bv w) := prim.adc   w x y b
def bswap       {w:ℕ} (v : expression (bv w))                        : expression (bv w) := prim.bswap w v
def bit_or            (x y : expression bit)                         : expression bit    := prim.bit_or  x y
def bit_and           (x y : expression bit)                         : expression bit    := prim.bit_and x y
def bit_xor           (x y : expression bit)                         : expression bit    := prim.bit_xor x y
def bv_nat (w:ℕ) (x : ℕ) : expression (bv w) := prim.bv_nat w x

def read_addr {tp:type} : addr tp → expression tp
| (addr.arg idx) := expression.read_arg idx tp

def of_reg {tp:type} : reg tp → expression tp
| (reg.concrete r) := expression.get_reg r
| (reg.arg a) := expression.read_arg a tp

instance addr_is_expression (tp:type) : has_coe (addr tp) (expression tp) :=
⟨ expression.read_addr ⟩



instance type_is_sort     : has_coe_to_sort type := ⟨Type, expression⟩
instance all_reg_is_expression : has_coe1 reg expression := ⟨λ_, expression.of_reg⟩

end expression

protected
def expression.imm : Π{tp:type}, imm tp → expression tp
| ._ (@imm.arg i tp) := expression.imm_arg i tp

instance expression.imm_is_expression (tp:type) : has_coe (imm tp) (expression tp) := ⟨expression.imm⟩

-- Operations on expressions

def slice {w:nat_expr} (x:expression (bv w)) (u:nat_expr) (l:nat_expr)
: expression (bv (u+1-l)) := prim.slice w u l x

def trunc {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.trunc w o x

def bsf {w:nat_expr} (x: bv w) : bv w := prim.bsf w x

def bsr {w:nat_expr} (x: bv w) : bv w := prim.bsr w x

def sext {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.sext w o x

def uext {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.uext w o x

def neq {tp:type} (x y : tp) : bit := prim.neq tp x y

def eq {tp:type} (x y : tp) : bit := prim.eq tp x y

def bit_one  : bit := prim.bit_one
def bit_zero : bit := prim.bit_zero

instance bv_has_mul (w:nat_expr) : has_mul (bv w) := ⟨λx y, prim.mul w x y⟩

-- Add two 80-bit numbers using the current x87 floating point control.
def x87_fadd (x y : x86_80) : x86_80 := prim.x87_fadd x y

instance float_extends_to_80  : has_coe float  x86_80 := ⟨prim.float_to_x86_80⟩

instance double_extends_to_80 : has_coe double x86_80 := ⟨prim.double_to_x86_80⟩

-- These are lossless conversions.
instance bv_to_x86_80  (w:one_of [16,32]) : has_coe (bv w) x86_80 := ⟨prim.bv_to_x86_80 w⟩

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
| streg (idx : fin 8) : lhs x86_80

namespace lhs

def of_addr {tp:type} : addr tp → lhs tp
| (addr.arg idx) := lhs.write_arg idx tp

def of_reg {tp:type} : reg tp → lhs tp
| (reg.concrete r) := lhs.set_reg r
| (reg.arg idx) := lhs.write_arg idx tp

end lhs


namespace expression
def of_lhs : Π{tp:type}, lhs tp → expression tp
| ._ (lhs.set_reg r) := expression.get_reg r
| ._ (lhs.write_addr a tp) := expression.read tp a
| ._ (lhs.write_arg idx tp) := expression.read_arg idx tp
| ._ (lhs.streg idx) := expression.streg idx

instance all_lhs_is_expression : has_coe1 lhs expression := ⟨λ_, expression.of_lhs⟩

instance lhs_is_expression (tp:type) : has_coe (lhs tp) (expression tp) := ⟨expression.of_lhs⟩

end expression


section

def reg8l (i:fin 16) : lhs (bv 8) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg8l
def reg8h (i:fin 16) : lhs (bv 8) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg8h

def al  := reg8l 0
def cl  := reg8l 1
def dl  := reg8l 2
def bl  := reg8l 3
def spl := reg8l 4
def bpl := reg8l 5
def sil := reg8l 6
def dil := reg8l 7
def ah  := reg8h 0

def reg16 (i:fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg16

def ax := reg16 0
def cx := reg16 1
def dx := reg16 2
def bx := reg16 3

def reg32 (i:fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg32

def eax := reg32 0
def ecx := reg32 1
def edx := reg32 2
def ebx := reg32 3

def reg64 (i:fin 16) := lhs.set_reg $ concrete_reg.gpreg i gpreg_type.reg64

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

def flagreg (i:fin 32) := lhs.set_reg $ concrete_reg.flagreg i

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
| unsupported (msg:string) : event
| pop_x87_register_stack : event
| call (addr: bv 64) : event
| jmp  (addr: bv 64) : event
| branch : expression bit → bv 64 → event
| hlt : event
| xchg {w : nat_expr} (addr1: bv w) (addr2: bv w) : event

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
| set_aligned    {tp:type} (l:lhs tp) (v:expression tp) (alignment:nat_expr) : action
-- Define a local variable for an expression.
| local_def {tp:type} (idx:nat) (v:expression tp) : action
| event (e:event) : action

--- Mark an lhs as undefined
def action.set_undef {tp:type} (l:lhs tp) : action := action.set l (expression.undef tp)

--- Conditionally mark an lhs as undefined
def action.set_undef_cond {tp:type} (l:lhs tp) (c: expression bit) : action :=
  action.set_cond l c (expression.undef tp)

------------------------------------------------------------------------
-- binding

inductive binding
| one_of : list nat → binding
| reg  : type → binding
| addr : type → binding
| imm  : type → binding
| lhs  : type → binding
| expression : type → binding

------------------------------------------------------------------------
-- context

structure context :=
(bindings : list binding)

def context.length (c:context) : arg_index := c.bindings.length

def context.add (b:binding) (ctx:context) : context :=
{ bindings := b :: ctx.bindings }

instance : has_insert binding context := ⟨context.add⟩

instance : has_emptyc context :=
⟨{bindings := []}⟩

------------------------------------------------------------------------
-- Patterns

structure pattern :=
(context : context)
(actions : list action)

------------------------------------------------------------------------
-- instruction

structure instruction :=
(mnemonic:string)
(patterns:list pattern)

------------------------------------------------------------------------
-- is_bound_var

-- Class for types that may be used as arguments in defining semantics.
class is_bound_var (tp:Type) :=
(to_binding{} : binding)
(mk_arg{} : arg_index → tp)

instance one_of_is_bound_var (range:list nat) : is_bound_var (one_of range) :=
{ to_binding := binding.one_of range
, mk_arg := one_of.var
}

instance reg_is_bound_var (tp:type) : is_bound_var (reg tp) :=
{ to_binding := binding.reg tp
, mk_arg := λi, reg.arg i
}

instance addr_is_bound_var (tp:type) : is_bound_var (addr tp) :=
{ to_binding := binding.addr tp
, mk_arg := λi, addr.arg i
}

instance imm_is_bound_var (tp:type) : is_bound_var (imm tp) :=
{ to_binding := binding.imm tp
, mk_arg := λi, imm.arg i
}


instance lhs_is_bound_var (tp:type) : is_bound_var (lhs tp) :=
{ to_binding := binding.lhs tp
, mk_arg := λi, lhs.write_arg i tp
}

instance expression_is_bound_var (tp:type) : is_bound_var (expression tp) :=
{ to_binding := binding.expression tp
, mk_arg := λi, expression.read_arg i tp
}

------------------------------------------------------------------------
-- semantics

structure semantics_state : Type :=
-- Actions seen so far in reverse order.
(actions : list action)
-- Number of local constants to use.
(local_variable_count : nat)

namespace semantics_state

def init : semantics_state :=
{ actions := []
, local_variable_count := 0
}

end semantics_state

structure semantics (α:Type) :=
(monad : state semantics_state α)

instance : monad semantics :=
{ pure := λ_ x, { monad := pure x }
, bind := λ_ _ m h, { monad := m.monad >>= λv, (h v).monad }
, map := λ_ _ f m, { monad := f <$> m.monad }
}

namespace semantics

--- Get the index to use for the next local variable.
protected
def next_local_index : semantics nat :=
  { monad := do
      s ← state_t.get,
      state_t.put {s with local_variable_count := s.local_variable_count + 1 },
      return s.local_variable_count
  }

--- Add an action to the list of actions.
protected
def add_action (e:action) : semantics unit :=
  { monad := state_t.modify (λs, { s with actions := e :: s.actions}) }

def record_event (e:event) : semantics unit :=
  semantics.add_action (action.event e)

-- Record that some code path is unsupported.
def unsupported (msg:string) := record_event (event.unsupported msg)

--- Set the expression of the left-hand side to the expression.
def set {tp:type} (l:lhs tp) (v:expression tp) : semantics unit :=
  semantics.add_action (action.set l v)

--- Set the expression of the left-hand side to the expression and respect alignment.
def set_aligned {tp:type} (l:lhs tp) (v:expression tp) (a:ℕ): semantics unit :=
  semantics.add_action (action.set_aligned l v a)

def set_cond {tp:type} (l:lhs tp) (c: expression bit) (v:expression tp) : semantics unit :=
  semantics.add_action (action.set_cond l c v)

--- Evaluate the given expression and return a local expression that will not mutate.
def eval {tp : type} (v:expression tp) : semantics (expression tp) := do
  idx ← semantics.next_local_index,
  semantics.add_action (action.local_def idx v),
  return (expression.get_local idx tp)

protected
def run (m:semantics unit) : list action := do
  (m.monad.run semantics_state.init).snd.actions.reverse

end semantics

------------------------------------------------------------------------
-- pattern_def

-- Class for functions of form λ... -> semantics unit
--
-- This is used to define patterns with lambdas to bind arguments.  The context variable
-- is needed so that we can infer how many variables have been bound outside of the
-- current context.
class pattern_def (ctx : context) (tp:Type) :=
{ define{} : tp → pattern }

instance semantics_is_pattern_def (ctx : context)
: pattern_def ctx (semantics unit) := { define := λm,
    { context := ctx
    , actions := semantics.run m
    }
  }

instance pi_is_pattern_def
  (tp:Type)
  [is_bound_var tp]
  (ctx:context)
  (β:tp → Type)
  [pattern_def (insert (is_bound_var.to_binding tp) ctx) (β (is_bound_var.mk_arg ctx.length))]
: pattern_def ctx (Π(w: tp), β w) :=
{ define := λf, do
    pattern_def.define (insert (is_bound_var.to_binding tp) ctx) (f (is_bound_var.mk_arg ctx.length))
}

-- Contains a list of patten matches defined using a monadic syntax.
def pattern_list : Type → Type := state (list pattern)

instance pattern_list_is_monad : monad pattern_list :=
begin
  simp [pattern_list],
  apply_instance,
end

-- Record pattern in current instruction
def mk_pattern {α:Type} [h : pattern_def ∅ α] (x:α) : pattern_list unit := do
  state_t.modify (list.cons (pattern_def.define ∅ x))

------------------------------------------------------------------------
-- definst

-- Create an instruction definition from mnemonic name and likst of patterns.
def definst (mnem:string) (pat: pattern_list unit) : instruction :=
{ mnemonic := mnem
, patterns := (pat.run []).snd.reverse
}

end x86
