import .basic
import galois.category.combinators
import galois.category.except
import galois.data.rbmap

------------------------------------------------------------------------
-- Semantics

namespace smt2

namespace semantics

inductive binding : Type 1
| declare_fun (nm:symbol) (args:list sort) (res:sort) : binding
| define_fun  (nm:symbol) (args:list (symbol × sort)) (res:sort) (rhs : term res) : binding

/-- State built up so far in generating an SMT file -/
structure context : Type 1 :=
-- Map of symbols created so far.  TODO:
(defined_symbols : rbmap symbol unit)
-- List of bindings
(bindings : list binding)
-- Conjunction of all asserted propositions
(asserted : Prop)
-- Conjunction of what's been asserted and had check-sat called on.
(checked : Prop)

namespace context

def initial : context :=
{ defined_symbols := mk_rbmap _ _
, bindings := []
, asserted := true
, checked := true
}

/-- Low-level utility that adds a binding. -/
def add_binding (b:binding) (s:context) := { s with bindings := b::s.bindings }

end context
end semantics


@[reducible]
def semantics : Type 1 → Type 1 := state_t semantics.context (except string)

namespace semantics

universe u

/-- Given a proposition @p@ that expects a model with the symbol
    in the binding @b@ defined, this calls p by adding the symbol to it.
-/
def quantify_binding {l:logic} : model l → binding → (model l → Prop) → Prop
| mdl (binding.declare_fun sym args tp) p := do
   ∀(x : l.fun_domain args tp), p (mdl.bind sym x)
| mdl (binding.define_fun sym args tp rhs) p := do
   let val := mdl.fun_value args rhs in
   p (mdl.bind sym val)


def quantify_bindings {l:logic} : list binding → (model l → Prop) → Prop
| [] p := p ∅
| (b::r) p := do
  quantify_bindings r (λmdl, quantify_binding mdl b p)

/-- Registers that a symbol is defined. -/
def register_symbol (nm:symbol) : semantics punit := do
  -- Check symbol is valid
  pwhen (nm.is_valid = ff) (throw ("Invalid name: " ++ nm)),
  -- Check symbol is not already defined
  s ← get,
  pwhen (nm ∈ s.defined_symbols) (throw ("Already defined: " ++ nm)),
  -- Insert symbol into defined_symbols
  put $ { s with defined_symbols := s.defined_symbols.insert nm () }

/-- Assert a term is true. -/
def assert {l:logic} (p:term bool) : semantics punit := do
 modify $ λs,
   { s with asserted
     := s.asserted
       ∧ quantify_bindings s.bindings (λm, eq.rec (p.interp m) l.prop_is_bool_type)
   }

/-- Declare a function -/
def declare_fun (nm:symbol) (args:list sort) (res:sort) : semantics punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.declare_fun nm args res)

/-- Define a function in terms of inputs -/
def define_fun (nm:symbol) (args:list (symbol × sort)) {res:sort} (rhs : term res)
: semantics punit := do
  register_symbol nm,
  modify $ context.add_binding (binding.define_fun nm args res rhs)

/-- Declare a constant with the given name -/
def declare_const (nm:symbol) (res:sort) := declare_fun nm [] res

/-- Declare a constant with the given name -/
def define_const (nm:symbol) {res:sort} (rhs:term res) := define_fun nm [] rhs

/-- Invoke check-sat command -/
def check_sat : semantics punit := do
  modify $ λctx, { ctx with checked := ctx.checked ∧ ctx.asserted }

end semantics
end smt2
