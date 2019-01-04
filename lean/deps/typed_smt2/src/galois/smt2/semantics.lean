import .interface
import galois.category.combinators
import galois.category.except
import galois.data.list
import galois.data.rbmap

------------------------------------------------------------------------
-- Semantics

namespace smt2

namespace semantics

inductive binding : Type 1
| declare_fun (nm:symbol) (args:list sort) (res:sort) : binding
| define_fun  (nm:symbol) (args:list (symbol × sort)) (res:sort) (rhs : term res) : binding

/-- State built up so far in generating an SMT file -/
structure context (l:logic) : Type 1 :=
-- Map of symbols created so far.  TODO:
(defined_symbols : rbmap symbol unit)
-- List of bindings
(bindings : list binding)
-- Conjunction of all asserted propositions
(asserted : list (term bool))
-- List of propositions we called check_sat with;  most recent first.
(checked : list Prop)

namespace context

def initial (l:logic) : context l :=
{ defined_symbols := mk_rbmap _ _
, bindings := []
, asserted := []
, checked := []
}

/-- Low-level utility that adds a binding. -/
def add_binding {l:logic} (b:binding) (s:context l) : context l :=
  { s with bindings := b::s.bindings }

end context
end semantics

def semantics (l:logic) : Type 1 → Type 1 := state_t (semantics.context l) (except string)

namespace semantics

instance (l:logic) : monad (semantics l) :=
by { unfold semantics, apply_instance }

instance (l:logic) : monad_except string (semantics l) :=
by { unfold semantics, apply_instance }

instance (l:logic) : monad_state (context l) (semantics l) :=
by { unfold semantics, apply_instance }

universe u

/-- Given a proposition @p@ that expects a model with the symbol
    in the binding @b@ defined, this calls p by adding the symbol to it.
-/
def quantify_binding {l:logic} : model l → binding → (model l → Prop) → Prop
| mdl (binding.declare_fun sym args tp) p := do
   ∃(x : l.fun_domain args tp), p (mdl.bind sym x)
| mdl (binding.define_fun sym args tp rhs) p := do
   let val := mdl.fun_value args rhs in
   p (mdl.bind sym val)

/-- Generate a model from a list of bindings and obtain a proposition. -/
def quantify_bindings {l:logic} : list binding → (model l → Prop) → Prop
| [] p := p ∅
| (b::r) p := do
  quantify_bindings r (λmdl, quantify_binding mdl b p)

/-- Registers that a symbol is defined. -/
def register_symbol {l:logic} (nm:symbol) : semantics l punit := do
  -- Check symbol is not already defined
  s ← get,
  pwhen (nm ∈ s.defined_symbols) (throw ("Already defined: " ++ repr nm)),
  -- Insert symbol into defined_symbols
  put $ { s with defined_symbols := s.defined_symbols.insert nm () }


protected
def interp_bool {l:logic} (m:model l) (p:term bool) : Prop := eq.rec (p.interp m) l.prop_is_bool_type

/-- Assert a term is true. -/
protected
def assert {l:logic} (p:term bool) : semantics l punit := do
 modify $ λctx,
   { ctx with asserted := p :: ctx.asserted
   }

/-- Declare a function -/
protected
def declare_fun {l:logic} (nm:symbol) (args:list sort) (res:sort) : semantics l punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.declare_fun nm args res)

/-- Define a function in terms of inputs -/
protected
def define_fun {l:logic} (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: semantics l punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.define_fun nm args res rhs)

/-- Invoke check-sat-assuming command -/
protected
def check_sat_assuming {l:logic} (preds : list (term bool)) : semantics l punit := do
  modify $ λctx,
  -- Build list containing previous assertions plus current predicates
  let all_preds := list.reverse_core ctx.asserted preds in
  let p := quantify_bindings ctx.bindings (λ(m:model l), (all_preds.map (semantics.interp_bool m)).forall_prop) in
      { ctx with checked := p :: ctx.checked }

/-- Invoke check-sat command -/
protected
def check_sat {l:logic} : semantics l punit := semantics.check_sat_assuming []

instance (l:logic) : is_generator (semantics l) :=
{ assert := semantics.assert
, declare_fun := semantics.declare_fun
, define_fun := semantics.define_fun
}

/--
This runs the semantics monad and either returns an error due to API
misuse or the proposition that was asserted.
-/
protected
def run_and_collect_unsat {l:logic} (m:semantics l punit) : except string Prop :=
  let f (r:punit × context l) : Prop := (r.snd.checked.map (λp, p = false)).forall_prop in
  (m.run (context.initial l)).map_poly f

end semantics

end smt2
