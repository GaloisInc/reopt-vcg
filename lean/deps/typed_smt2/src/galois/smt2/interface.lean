import .basic

universes u v

namespace smt2

/-- This is a class for generating SMTLIB definitions -/
class is_generator (m : Type u → Type v) extends monad m :=
-- Assert a Boolean term is true.
(assert {} : term Bool → m punit)
-- Declare a function
(declare_fun {} : symbol → list sort → sort → m punit)
-- Declare a constant with the given name
(declare_const {} : symbol → sort → m punit := λnm, declare_fun nm [])
-- Declare a function
(define_fun {} : symbol → list (symbol × sort) → Π(r:sort), term r → m punit)
-- Declare a function
(check_sat {} : m punit)

section
parameter {m : Type u → Type v}
parameter [h:is_generator m]
include h
open is_generator

/- Assert predicate -/
def assert : term Bool → m punit := assert

/- Declare a function. -/
def declare_fun : symbol → list sort → sort → m punit := declare_fun

/- Declare a constant with the given name. -/
def declare_const : symbol → sort → m punit := declare_const

/- Declare a function. -/
def define_fun : symbol → list (symbol × sort) → Π(r:sort), term r → m punit := define_fun

/- Declare a function. -/
def check_sat : m punit := check_sat

end

end smt2
