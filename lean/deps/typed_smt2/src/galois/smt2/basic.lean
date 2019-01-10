/-
This declares sorts, terms, and semantics for generating SMTLIB
expressions and reasoning about their interpretation.
-/
import data.bitvec
import galois.category.except
import galois.data.bool
import galois.data.buffer
import galois.data.list
import galois.data.option
import galois.logic
import galois.sexpr

import .atom

universes u v

/- A list whose element types are constructed from applying a function to another list. -/
inductive indexed_list {α:Type u} (f:α → Sort v) : list α → Sort (max (u+1) v)
| nil {} : indexed_list []
| cons {h:α} {r:list α} : f h → indexed_list r → indexed_list (h::r)

namespace indexed_list
section

parameter {α:Type u}
parameter {f:α → Sort v}

/- Return the nth_le element in the list. -/
def nth_le : Π{l:list α}, indexed_list f l → Π(i:ℕ) (i_lt:i < l.length), f (l.nth_le i i_lt)
| ._ nil      n     h := absurd h (nat.not_lt_zero n)
| ._ (cons a l) 0     h := a
| ._ (cons a l) (n+1) h := nth_le l n (nat.le_of_succ_le_succ h)

end
end indexed_list

------------------------------------------------------------------------
-- SMT theory

namespace smt2

------------------------------------------------------------------------
-- ident_arg

/-
A identifier arg represents either a number or a
symbol (possibly with arguments provided).
-/
inductive ident_arg : Type
| nat   {} : ℕ → ident_arg
| sort  {} : symbol → list ident_arg → ident_arg

namespace ident_arg

------------------------------------------------------------------------
-- is_child

/- is_child c x holds if one ident_arg appears as an argument to another. -/
inductive is_child : ident_arg → ident_arg → Prop
| mem : Π{x : ident_arg} {nm : symbol} {args : list ident_arg}
          (is_mem : x ∈ args),
          is_child x (ident_arg.sort nm args)

/- Prove is_child relationship is well-founded. -/
def is_child.wf : well_founded is_child :=
begin
  apply well_founded.intro,
  intro z,
  apply well_founded.fix (sizeof_measure_wf ident_arg) _ z,
  intros y rec,
  dsimp [sizeof_measure, measure, inv_image] at rec,
  apply acc.intro,
  intros x x_lt_y,
  cases y with n nm args,
  { cases x_lt_y, },
  { cases x_lt_y with a b c x_in_args,
    apply rec,
    simp [sizeof, has_sizeof.sizeof, ident_arg.sizeof, nat.succ_add ],
    transitivity, exact (list.mem_sizeof x_in_args),
    apply nat.lt_of_le_of_lt (nat.le_add_left _ nm.sizeof),
    exact (nat.succ_le_succ (nat.le_refl _)),
  },
end

------------------------------------------------------------------------
-- fixpoint function based on is_child.

section

parameter {C : ident_arg → Sort _}
parameter (nat_eval : Π(n:ℕ), C (nat n))
parameter (sort_eval : Π(nm:symbol) (args:list ident_arg),
               (Π(y : ident_arg), y ∈ args → C y)
               → C (sort nm args))

def fix.f
  : Π (x : ident_arg), (Π (y : ident_arg), ident_arg.is_child y x → C y) -> C x
| (nat n) _ := nat_eval n
| (sort nm args) ind := sort_eval nm args (λy h, ind y (is_child.mem h))

@[elab_with_expected_type]
def fix : Π(x : ident_arg), C x := well_founded.fix is_child.wf fix.f

end

------------------------------------------------------------------------
--

/-- Convert a ident_arg to an s-expression. -/
protected
def to_sexpr : ident_arg → sexpr atom :=
  let num (n:ℕ) := sexpr.atom (atom.numeral n) in
  let app (nm : symbol) (args : list ident_arg) rec :=
        sexpr.parens
          (sexpr.atom (atom.symbol nm) :: args.map_with_mem rec) in
  fix num app

def decidable_eq.nat (m:ℕ) : Π(y:ident_arg), decidable (nat m = y)
| (nat n) :=
  if p : m = n then
    is_true (congr_arg nat p)
  else
    is_false (λh, p (ident_arg.nat.inj h))
| (sort nm args) := is_false (by contradiction)

def decidable_eq.app (nm : symbol) (args : list ident_arg)
        (rec : Π(y:ident_arg), y ∈ args → Πz, decidable (y = z))
 : Π(y:ident_arg), decidable (sort nm args = y)
 | (nat n) := is_false (by contradiction)
 | (sort ynm yargs) :=
   if pnm : nm = ynm then
     let p (xe) (xmem) (ye) (ymem : ye ∈ yargs)
          : decidable (xe = ye) := rec xe xmem ye in
     match list.has_dec_eq_with_mem args yargs p with
     | is_true pr   := is_true (eq.subst pnm (eq.subst pr rfl))
     | is_false npr := is_false (λh, npr (ident_arg.sort.inj h).right)
     end
   else
     is_false (λh, pnm (ident_arg.sort.inj h).left)

protected
def has_dec_eq : decidable_eq ident_arg :=
  fix decidable_eq.nat decidable_eq.app

instance : decidable_eq ident_arg := ident_arg.has_dec_eq
instance : has_coe ℕ ident_arg := ⟨ident_arg.nat⟩
end ident_arg

------------------------------------------------------------------------
-- sort

/--
Sorts in SMTLIB.
-/
inductive sort  : Type
| Bool : sort
| BitVec (w:ℕ) : sort

namespace sort

protected def to_sexpr : sort → sexpr atom
| Bool := symbol.of_string "Bool"
| (BitVec w) := sexpr.parens [reserved_word.of_string "_", symbol.of_string "BitVec", atom.numeral w]

instance sort_is_sexpr : has_coe sort (sexpr atom) := ⟨sort.to_sexpr⟩

instance : decidable_eq sort := by tactic.mk_dec_eq_instance

def domain : sort → Type
| Bool := bool
| (BitVec w) := bitvec w

def default : Π(s:sort), s.domain
| sort.Bool := tt
| (BitVec w) := (0 : bitvec w)

end sort

export sort(Bool)
export sort(BitVec)

------------------------------------------------------------------------
-- rank

/- The input sorts and output associated with a user-defined symbol. -/
structure rank : Type :=
(inputs : list sort)
(return : sort)

namespace rank
/- Returns the type of values in the domain. -/
def domain (r:rank) : Type := r.inputs.foldr (λa r, a.domain → r) r.return.domain
end rank

namespace sort
/- Returns the rank with no arguments and the given sort. -/
protected def to_rank (s:sort) : rank := ⟨[],s⟩
instance sort_is_rank : has_coe sort rank := ⟨sort.to_rank⟩
end sort

------------------------------------------------------------------------
-- interpretation

/-- This represents a mapping from constants to the associated sybol. -/
structure interpretation : Type :=
(var_map : rbmap symbol (sigma rank.domain))

namespace interpretation

protected
def lookup_var (i:interpretation) (nm:symbol) (s:sort) : option s.domain :=
  match i.var_map.find nm with
  | (some ⟨⟨[],t⟩,d⟩) :=
    if h : t = s then
      some (cast (congr_arg sort.domain h) d)
    else
      none
  | _ := none
  end

protected
def bind (i:interpretation) (nm:symbol) (r:rank) (d:r.domain) : interpretation
:= { i with var_map := i.var_map.insert nm ⟨r, d⟩ }

protected def empty : interpretation := { var_map := mk_rbmap _ _ _ }

instance : has_emptyc interpretation := ⟨interpretation.empty⟩

end interpretation

------------------------------------------------------------------------
-- term

/- Defines a term in our logic. -/
structure term (s:sort) : Type :=
(to_sexpr : sexpr atom)
(interp : interpretation → s.domain)

namespace term
instance (s:sort) : has_coe (term s) (sexpr atom) := ⟨term.to_sexpr⟩
end term

/- Return the rank associated with a function with the given arguments and return type. -/
def arg_rank (args: list (symbol × sort)) (r:sort) : rank := ⟨args.map prod.snd, r⟩

/- Return the function defined by the given arguments and term.  -/
def function_def
: Π(i:interpretation) (args:list (symbol × sort)) {r:sort} (rhs : term r), (arg_rank args r).domain
| i [] r rhs := rhs.interp i
| i (⟨nm,s⟩::l) r rhs := λ(x:s.domain), function_def (i.bind nm s.to_rank x) l rhs

def var (nm:symbol) (s:sort) : term s :=
{ to_sexpr := nm
, interp   := λctx,
   match ctx.lookup_var nm s with
   | (some v) := v
   | none := s.default
   end
}

------------------------------------------------------------------------
-- Apply predicates

/- Apply function to elements in list with a left associative operation. -/
def apply_left_assoc (m:interpretation) {s:sort}
      (f : s.domain → s.domain → s.domain)
      (x:term s) (l:list (term s)) : s.domain :=
  list.foldl (λa (b:term s), f a (b.interp m)) (x.interp m) l

/- Apply function to elements in list with a right associative operation. -/
def apply_right_assoc (m:interpretation) {s:sort} (f : s.domain → s.domain → s.domain)
      (l:list (term s)) (x:term s) : s.domain :=
  list.foldr (λ(a:term s) b, f (a.interp m) b) (x.interp m) l

/- Apply predicate to each two pair of elements in list and return conjunction. -/
def apply_chainable {α} (p : α → α → bool) : α → list α → bool
| x [] := tt
| x (h::r) := p x h && apply_chainable h r

/- Apply predicate to all elements in list, and return conjunction. -/
def all_band {α} (p : α → bool) : list α → bool
| [] := tt
| (h::r) :=  p h && all_band r

/- Apply predicate to each two pair of elements in list and return conjunction. -/
def apply_pairwise {α} (p : α → α → bool) : list α → bool
| [] := tt
| (h::r) := all_band (p h) r && apply_pairwise r

------------------------------------------------------------------------
-- Core theory

/-- True predicate. -/
protected
def true : term Bool :=
{ to_sexpr := sexpr.of_string "true"
, interp := λm, tt
}

/-- False predicate. -/
protected
def false : term Bool :=
{ to_sexpr := sexpr.of_string "false"
, interp := λm, ff
}

/-- False predicate. -/
protected
def not (x : term Bool) : term Bool :=
{ to_sexpr := sexpr.parens [sexpr.of_string "false", x]
, interp := λm, bnot (x.interp m)
}

protected
def implies (c : list (term Bool)) (p : term Bool) : term Bool :=
{ to_sexpr := sexpr.parens (sexpr.of_string "=>" :: (c.map term.to_sexpr ++ [p]))
, interp := λm, apply_right_assoc m bimplies c p
}

protected
def and_all_interp (m:interpretation) (l:list (term Bool)) :=
  l.foldl (λa (b:term Bool), band a (b.interp m)) tt

protected
def and_all : list (term Bool) → term Bool
| [] := smt2.true
| (h::r) :=
  { to_sexpr := sexpr.parens (sexpr.of_string "and" :: (h::r).map term.to_sexpr)
  , interp := λm, smt2.and_all_interp m (h::r)
  }

/-- Return true if any terms in the arguments are true. -/
protected
def any : list (term Bool) → term Bool
| [] := smt2.false
| (h::r) :=
  { to_sexpr := sexpr.parens (sexpr.of_string "or" :: (h::r).map term.to_sexpr)
  , interp := λm, apply_left_assoc m bor h r
  }

/-- Holds if an odd number of Booleans in the list are true. -/
protected
def xor_list : list (term Bool) → term Bool
| [] := smt2.false
| [h] := h
| (h::r) :=
  { to_sexpr := sexpr.parens (sexpr.of_string "xor" :: (h::r).map term.to_sexpr)
  , interp := λm, apply_left_assoc m bxor h r
  }

/-- Return true if all terms in list are equal. -/
def all_equal {s:sort} [h : decidable_eq s.domain] : list (term s) → term Bool
| [] := smt2.true
| [x] := smt2.true
| (x::l) :=
  { to_sexpr := sexpr.parens (sexpr.of_string "=" :: x :: l.map term.to_sexpr)
  , interp := λm, apply_chainable (λ(x y : term s), decidable.to_bool (x.interp m = y.interp m)) x l
  }

/-- Assert all terms in list are pairwise distinct. -/
protected
def distinct {s:sort} [h : decidable_eq s.domain] : list (term s) → term Bool
| [] := smt2.true
| [x] := smt2.true
| l := { to_sexpr := sexpr.parens (sexpr.of_string "=" :: l.map term.to_sexpr)
       , interp   := λm, apply_pairwise (λ(x y : term s), decidable.to_bool (x.interp m ≠ y.interp m)) l
       }

/-- Return one term or another depending on Boolean predicate. -/
protected
def ite {s:sort} (c : term Bool) (x y : term s) : term s :=
{ to_sexpr := sexpr.parens [sexpr.of_string "ite", c, x, y]
, interp   := λm, cond (c.interp m) (x.interp m) (y.interp m)
}

def binding := symbol × sigma term

namespace binding

protected
def to_sexpr : binding → sexpr atom
| (nm, ⟨s, t⟩) := sexpr.parens [nm, t]

instance : has_coe binding (sexpr atom) := ⟨binding.to_sexpr⟩

end binding

/- Extend the model with a list of bindings. -/
def extend_model (scope:interpretation) : interpretation → list binding → interpretation
| i [] := i
| i ((nm, ⟨s, t⟩)::r) := extend_model (i.bind nm (s.to_rank) (t.interp scope)) r

/- Generate a term that with let bindings. -/
protected
def term_let {s:sort} : list binding → term s → term s
| [] t := t
| l t :=
   { to_sexpr := sexpr.parens [sexpr.of_string "let", sexpr.parens (l.map binding.to_sexpr), t]
   , interp := λm, t.interp (extend_model m m l)
  }

end smt2
