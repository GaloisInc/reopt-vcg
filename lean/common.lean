import .coe1

-- This tries to prove a property by just running the evaluator.
meta def dec_trivial_tac : tactic unit := do
  tgt ← tactic.target,
  tactic.apply $ (`(@of_as_true) : expr) tgt,
  tactic.triv

def unlines : list string → string := list.foldr (λx r, x ++ "\n" ++ r) ""

-- Library for buidling s expressions
namespace sexp

def app (s:string) (l:list string) := "(" ++ s ++ list.foldr (λx r, " " ++ x ++ r) ")" l

-- Pretty print
def from_list : list string → string
| [] := "()"
| (s::l) := app s l

end sexp

def paren_if : bool → string → string
| tt s := "(" ++ s ++ ")"
| ff s := s

------------------------------------------------------------------------
-- Coercisions

namespace mc_semantics

------------------------------------------------------------------------
-- arg_index

@[reducible]
def arg_index := nat

def arg_index.pp (idx:arg_index) : string := "arg" ++ idx.repr

------------------------------------------------------------------------
-- nat_expr

inductive nat_expr : Type
| lit : nat → nat_expr
| var : arg_index → nat_expr
| add : nat_expr → nat_expr → nat_expr
| sub : nat_expr → nat_expr → nat_expr
| mul : nat_expr → nat_expr → nat_expr

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

instance : has_zero nat_expr := ⟨nat_expr.zero⟩
instance : has_one nat_expr := ⟨nat_expr.one⟩
instance : has_add nat_expr := ⟨nat_expr.do_add⟩
instance : has_sub nat_expr := ⟨nat_expr.do_sub⟩
instance : has_mul nat_expr := ⟨nat_expr.do_mul⟩

protected def pp : nat_expr → string
| (lit x) := x.repr
| (var x) := x.pp
| (add x y) := sexp.app "addNat" [x.pp, y.pp]
| (sub x y) := sexp.app "subNat" [x.pp, y.pp]
| (mul x y) := sexp.app "mulNat" [x.pp, y.pp]

instance : has_repr nat_expr := ⟨nat_expr.pp⟩

instance nat_coe_nat_expr : has_coe ℕ nat_expr := ⟨λx, lit x⟩

end nat_expr

------------------------------------------------------------------------
-- one_of

inductive one_of (l:list ℕ) : Type
| var{} : arg_index → one_of

namespace one_of

def to_nat_expr {l:list ℕ} : one_of l → nat_expr
| (one_of.var i) := nat_expr.var i

protected def pp {l:list ℕ} (x:one_of l) := x.to_nat_expr.pp

instance (l:list ℕ) : has_coe (one_of l) nat_expr :=
⟨ one_of.to_nat_expr ⟩


end one_of

local notation ℕ := nat_expr

inductive type
| bv (w:ℕ) : type
| bit : type
| float  : type
| double : type
| x86_80 : type
-- A function from arg to res
| fn (arg:type) (res:type) : type

namespace type

protected
def pp' : Π(in_fun:bool), type → string
| _ (bv w) := sexp.app "bv" [w.pp]
| _ bit    := "bit"
| _ float  := "float"
| _ double := "double"
| _ x86_80 := "x86_80"
| in_fun (fn a r) :=
  if in_fun then
     a.pp' ff ++ " " ++ r.pp' tt
  else
     sexp.app "fun" [a.pp' ff, r.pp' tt]

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

local notation ℕ := nat_expr

-- Denotes the type of a register.
inductive gpreg_type : Type
| reg8l : gpreg_type
--| reg8h : gpreg_type
| reg16 : gpreg_type
| reg32 : gpreg_type
| reg64 : gpreg_type

namespace gpreg_type

@[reducible]
def width : gpreg_type → ℕ
| reg8l  := 8
--| reg8h  := 8
| reg16 := 16
| reg32 := 32
| reg64 := 64

end gpreg_type

-- Type for x86 registers
inductive reg : type → Type
| concrete_gpreg   (idx:fin 16) (tp:gpreg_type) : reg (bv (tp.width))
| concrete_flagreg (idx:fin 32) : reg bit

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

protected def repr : Π{tp:type}, reg tp → string
| ._ (concrete_gpreg idx tp) := "$" ++
  match tp with
  | gpreg_type.reg8l := list.nth_le reg.r8l_names idx.val idx.is_lt
  | gpreg_type.reg16 := list.nth_le reg.r16_names idx.val idx.is_lt
  | gpreg_type.reg32 := list.nth_le reg.r32_names idx.val idx.is_lt
  | gpreg_type.reg64 := list.nth_le reg.r64_names idx.val idx.is_lt
  end
| ._ (concrete_flagreg idx) := "$" ++
   match list.nth reg.flag_names idx.val with
   | (option.some nm) := nm
   | option.none :=  "REVERSED_" ++ idx.val.repr
   end

end reg

-- Denotes an address.
inductive addr (tp:type) : Type
| arg {} (idx: arg_index) : addr

namespace addr

protected def repr {tp:type} : addr tp → string
| (arg idx) := idx.pp

end addr

--- Expressions that may appear on the left-hand side of an assignment.
inductive lhs : type → Type
| reg {tp:type} (r:reg tp) : lhs tp
-- A value that must be an address.
| addr {tp:type} (a:addr tp) : lhs tp
-- An argument that may be either a register or address.
| arg (idx:arg_index) (tp:type) : lhs tp
-- ST reg with the offset relative to the current stack top value.
| streg (idx : fin 8) : lhs x86_80

namespace lhs

-- Pretty printer for lhs
protected def repr : Π {tp:type}, lhs tp → string
| _  (reg r) := r.repr
| ._ (addr a) := a.repr
| _  (arg idx tp) := idx.pp
| ._ (streg idx) := "st" ++ idx.val.repr

end lhs

section

def reg8l (i:fin 16) := lhs.reg $ reg.concrete_gpreg i gpreg_type.reg8l

def al  := reg8l 0
def cl  := reg8l 1
def dl  := reg8l 2
def bl  := reg8l 3
def spl := reg8l 4
def bpl := reg8l 5
def sil := reg8l 6
def dil := reg8l 7

def reg16 (i:fin 16) := lhs.reg $ reg.concrete_gpreg i gpreg_type.reg16

def ax := reg16 0
def cx := reg16 1
def dx := reg16 2
def bx := reg16 3

def reg32 (i:fin 16) := lhs.reg $ reg.concrete_gpreg i gpreg_type.reg32

def eax := reg32 0
def ecx := reg32 1
def edx := reg32 2
def ebx := reg32 3

def reg64 (i:fin 16) := lhs.reg $ reg.concrete_gpreg i gpreg_type.reg64

def rax := reg64 0
def rcx := reg64 1
def rdx := reg64 2
def rbx := reg64 3

def flagreg (i:fin 32) := lhs.reg $ reg.concrete_flagreg i

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

local infixr `.→`:30 := fn

-- This denotes primitive operations that are part of the semantics.
inductive prim : type → Type
-- `(add i)` returns the sum of two i-bit numbers.
| add (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- `(mul i)` returns the product of two i-bit numbers.
| mul (i:ℕ) : prim (bv i .→ bv i .→ bv i)
-- `(slice w u l)` takes bits `u` through `l` out of a `w`-bit number.
| slice (w:ℕ) (u:ℕ) (l:ℕ) : prim (bv w .→ bv (u+1-l))
-- `(sext i o)` sign extends an `i`-bit number to a `o`-bit number.
| sext  (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(uext i o)` unsigned extension of an `i`-bit number to a `o`-bit number.
| uext  (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(trunc i o)` truncates an `i`-bit number to a `o`-bit number.
| trunc (i:ℕ) (o:ℕ) : prim (bv i .→ bv o)
-- `(eq tp)` returns `true` if two values are equal.
| eq (tp:type) : prim (tp .→ tp .→ bit)
-- `(neq tp)` returns `true` if two values are not equal.
| neq (tp:type) : prim (tp .→ tp .→ bit)
-- `x87_fadd` adds two extended precision values using the flags in the x87 register.
| x87_fadd : prim (x86_80 .→ x86_80 .→ x86_80)
-- `float_to_x86_80` converts a float to an extended precision number (lossless)
| float_to_x86_80  : prim (float .→ x86_80)
-- `double_to_x86_80` converts a double to an extended precision number (lossless)
| double_to_x86_80 : prim (double .→ x86_80)
-- `bv_to_x86_80` converts a bitvector to an extended precision number (lossless)
| bv_to_x86_80  (w : one_of [16,32]) : prim (bv w .→ x86_80)

namespace prim

def pp : Π{tp:type}, prim tp → string
| ._ (add i) := "add " ++ i.pp
| ._ (mul i) := "mul " ++ i.pp
| ._ (slice w u l) := "slice " ++ w.pp ++ " " ++ u.pp ++ " " ++ l.pp
| ._ (sext i o) := "sext " ++ i.pp ++ " " ++ o.pp
| ._ (uext i o) := "uext " ++ i.pp ++ " " ++ o.pp
| ._ (trunc i o) := "trunc " ++ i.pp ++ " " ++ o.pp
| ._ (eq tp) := "eq " ++ tp.pp
| ._ (neq tp) := "neq " ++ tp.pp
| ._ x87_fadd := "x87_fadd"
| ._ float_to_x86_80 := "float_to_x86_80"
| ._ double_to_x86_80 := "double_to_X86_80"
| ._ (bv_to_x86_80 w) := "sext " ++ w.pp

end prim

-- Type for expressions that may denote a value.
inductive value : type → Type
-- Create a value our of a primitive
| primitive {rtp:type} (o:prim rtp) : value rtp
-- Apply a function to an argument.
| app {rtp:type} {tp:type} (f : value (type.fn tp rtp)) (a : value tp) : value rtp
  -- Get the value associated with the assignable value.
| get {tp:type} (l:lhs tp) : value tp
  -- Return the value in the local variable at the given index.
| get_local (idx:ℕ) (tp:type) : value tp

namespace value

instance (rtp:type) : has_coe (prim rtp) (value rtp) := ⟨value.primitive⟩

instance (a:type) (f:type) : has_coe_to_fun (value (type.fn a f)) :=
{ F := λ_, Π(y:value a), value f
, coe := app
}

instance (w:ℕ) : has_zero (value (bv w)) := sorry
instance (w:ℕ) : has_one  (value (bv w)) := sorry
instance (w:ℕ) : has_add  (value (bv w)) := sorry

protected
def is_app : Π{tp:type}, value tp → bool
| ._ (app _ _) := tt
| _ _ := ff

protected
def pp_args : Π{tp:type}, value tp → string
| ._ (primitive o) := o.pp
| ._ (app f a) := f.pp_args ++ " " ++ paren_if a.is_app a.pp_args
| ._ (get lhs) := lhs.repr
| ._ (get_local idx tp) := sexp.app "local" [idx.pp]

protected
def pp {tp:type} (v:value tp) := paren_if v.is_app v.pp_args

instance (tp:type) : has_repr (value tp) := ⟨value.pp⟩

instance addr_is_value (tp:type) : has_coe (addr tp) (value tp) :=
⟨ value.get ∘ lhs.addr ⟩

instance type_is_sort     : has_coe_to_sort type := ⟨Type, value⟩
instance all_lhs_is_value : has_coe1 lhs value := ⟨λ_, value.get⟩
instance lhs_is_value (tp:type) : has_coe (lhs tp) (value tp) := ⟨value.get⟩

end value

-- Operations on values

def slice {w:nat_expr} (x:value (bv w)) (u:nat_expr) (l:nat_expr)
: value (bv (u+1-l)) := prim.slice w u l x

def trunc {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.trunc w o x

def sext {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.sext w o x

def uext {w:nat_expr} (x: bv w) (o:nat_expr) : bv o := prim.uext w o x

def neq {tp:type} (x y : tp) : bit := prim.neq tp x y

instance bv_has_mul (w:nat_expr) : has_mul (bv w) := ⟨λx y, prim.mul w x y⟩

-- Add two 80-bit numbers using the current x87 floating point control.
def x87_fadd (x y : x86_80) : x86_80 := prim.x87_fadd x y

instance float_extends_to_80  : has_coe float  x86_80 := ⟨prim.float_to_x86_80⟩

instance double_extends_to_80 : has_coe double x86_80 := ⟨prim.double_to_x86_80⟩

-- These are lossless conversions.
instance bv_to_x86_80  (w:one_of [16,32]) : has_coe (bv w) x86_80 := ⟨prim.bv_to_x86_80 w⟩

------------------------------------------------------------------------
-- event

-- These are a type of action that may have side effects, but do
-- not return values.
inductive event
| syscall : event
| unsupported (msg:string) : event
| pop_x87_register_stack : event

namespace event

protected def pp : event → string
| syscall := "(syscall)"
| (unsupported msg) := "(unsupported " ++ msg ++ ")"
| pop_x87_register_stack := "(pop_x87_register_stack)"

end event

------------------------------------------------------------------------
-- action

-- Denotes updates to program state from register.
inductive action
| set {tp:type} (l:lhs tp) (v:value tp) : action
| local_def {tp:type} (idx:ℕ) (v:value tp) : action
| event (e:event) : action

namespace action

protected def repr : action → string
| (set l r)         := sexp.app "set" [l.repr, r.pp]
| (local_def idx v) := sexp.app "var" [idx.pp, v.pp]
| (event e) := e.pp

end action

------------------------------------------------------------------------
-- binding

inductive binding
| one_of : list nat → binding
| lhs : type → binding
| value : type → binding

namespace binding

def pp : binding → string
| (one_of l) := sexp.app "one_of" (nat.repr <$> l)
| (lhs tp) := sexp.app "lhs" [tp.pp]
| (value tp) := sexp.app "value" [tp.pp]

end binding

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

namespace pattern

private
def pp_bindings : nat → list binding → string
| i [] := ""
| i (b::r)
  := "  " ++ sexp.app "arg" [i.repr, b.pp] ++ "\n"
  ++ pp_bindings (i+1) r

private
def pp_action (m:action) : string := "  " ++ m.repr

protected
def pp (p:pattern) : string
  := "pattern\n"
  ++ pp_bindings 0 p.context.bindings.reverse
  ++ unlines (pp_action <$> p.actions)
  ++ "end_pat"

end pattern

------------------------------------------------------------------------
-- instruction

structure instruction :=
(mnemonic:string)
(patterns:list pattern)

namespace instruction

def repr (i:instruction) : string :=
  "instruction " ++ i.mnemonic ++ "\n"
   ++ unlines (pattern.pp <$> i.patterns)
   ++ "end instruction"

instance : has_repr instruction := ⟨instruction.repr⟩

end instruction

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

instance lhs_is_bound_var (tp:type) : is_bound_var (lhs tp) :=
{ to_binding := binding.lhs tp
, mk_arg := λi, lhs.arg i tp
}

instance value_is_bound_var (tp:type) : is_bound_var (value tp) :=
{ to_binding := binding.value tp
, mk_arg := λi, value.get (lhs.arg i tp)
}

------------------------------------------------------------------------
-- semantics

structure semantics_state : Type :=
-- Actions seen so far in reverse order.
(actions : list action)
-- Number of local constants to use.
(local_variable_count : ℕ)

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
def next_local_index : semantics ℕ :=
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

--- Set the value of the left-hand side to the value.
def set {tp:type} (l:lhs tp) (v:value tp) : semantics unit :=
  semantics.add_action (action.set l v)

--- Evaluate the given value and return a local value that will not mutate.
def eval {tp : type} (v:value tp) : semantics (value tp) := do
  idx ← semantics.next_local_index,
  semantics.add_action (action.local_def idx v),
  return (value.get_local idx tp)

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

def definst (mnem:string) (pat: pattern_list unit) : instruction :=
{ mnemonic := mnem
, patterns := (pat.run []).snd.reverse
}

end x86
