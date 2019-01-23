import galois.category.combinators
import galois.category.except
import galois.data.list
import galois.data.rbmap

import .interface

------------------------------------------------------------------------
-- Semantics

namespace smt2

namespace semantics

inductive binding : Type
| declare_fun {} (nm:symbol) (args:list sort) (res:sort) : binding
| define_fun  (nm:symbol) (args:list (symbol × sort)) (res:sort) (rhs : term res) : binding

/-- State built up so far in generating an SMT file -/
structure context  : Type :=
-- Map of symbols created so far.  TODO:
(defined_symbols : rbmap symbol unit)
-- List of bindings
(bindings : list binding)
-- Conjunction of all asserted propositions
(asserted : list (term Bool))
-- List of propositions we called check_sat with;  most recent first.
(checked : list Prop)

namespace context

def initial : context :=
{ defined_symbols := mk_rbmap _ _
, bindings := []
, asserted := []
, checked := []
}

/-- Low-level utility that adds a binding. -/
def add_binding (b:binding) (s:context) : context :=
  { s with bindings := b::s.bindings }

end context
end semantics

def semantics : Type → Type := state_t semantics.context (except string)

namespace semantics

section
local attribute [reducible] semantics
instance : monad semantics := by apply_instance
instance : monad_except string semantics := by apply_instance
instance : monad_state context semantics := by apply_instance
end

universe u

/-- Given a proposition @p@ that expects a model with the symbol
    in the binding @b@ defined, this calls p by adding the symbol to it.
-/
def quantify_binding : interpretation → binding → (interpretation → Prop) → Prop
| mdl (binding.declare_fun sym arg_sorts return_sort) p := do
   ∃(x : (rank.mk arg_sorts return_sort).domain), p (mdl.bind sym _ x)
| mdl (binding.define_fun sym args tp rhs) p := do
   p (mdl.bind sym _ (function_def mdl args rhs))

/-- Generate a model from a list of bindings and obtain a proposition. -/
def quantify_bindings : list binding → (interpretation → Prop) → Prop
| [] p := p ∅
| (b::r) p := do
  quantify_bindings r (λmdl, quantify_binding mdl b p)

/-- Registers that a symbol is defined. -/
def register_symbol (nm:symbol) : semantics punit := do
  -- Check symbol is not already defined
  s ← get,
  pwhen (nm ∈ s.defined_symbols) (throw ("Already defined: " ++ repr nm)),
  -- Insert symbol into defined_symbols
  put $ { s with defined_symbols := s.defined_symbols.insert nm () }


--protected
--def interp_bool (m:interpretation) (p:term Bool) : Prop := p.interp m

/-- Assert a term is true. -/
protected
def assert (p:term Bool) : semantics punit := do
 modify $ λctx,
   { ctx with asserted := p :: ctx.asserted
   }

/-- Declare a function -/
protected
def declare_fun (nm:symbol) (args:list sort) (res:sort) : semantics punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.declare_fun nm args res)

/-- Define a function in terms of inputs -/
protected
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: semantics punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.define_fun nm args res rhs)

/-- Invoke check-sat-assuming command -/
protected
def check_sat_assuming (preds : list (term Bool)) : semantics punit := do
  modify $ λctx,
  -- Build list containing previous assertions plus current predicates
  let all_preds := list.reverse_core ctx.asserted preds in
  let p := quantify_bindings ctx.bindings
               (λ(m:interpretation), smt2.and_all_interp m all_preds) in
      { ctx with checked := p :: ctx.checked }

/-- Invoke check-sat command -/
protected
def check_sat : semantics punit := semantics.check_sat_assuming []

instance : is_generator semantics :=
{ assert      := semantics.assert
, declare_fun := semantics.declare_fun
, define_fun  := semantics.define_fun
}

/--
This runs the semantics monad and either returns an error due to API
misuse or the proposition that was asserted.
-/
protected
def run_and_collect_unsat (m:semantics punit) : except string Prop :=
  let f (r:punit × context) : Prop := (r.snd.checked.map (λp, p = false)).forall_prop in
  (m.run context.initial).map_poly f

end semantics

end smt2
