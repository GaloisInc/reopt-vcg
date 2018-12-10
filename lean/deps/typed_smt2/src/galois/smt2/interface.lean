import .basic

universes u v

namespace smt2

/-- This is a class for generating SMTLIB definitions -/
class is_generator (m : Type u → Type v) extends monad m :=
(assert {} : term bool → m punit)
(declare_fun {} : symbol → list sort → sort → m punit)
(declare_const {} : symbol → sort → m punit := λnm, declare_fun nm [])
(define_fun {} : symbol → list (symbol × sort) → Π(r:sort), term r → m punit)

/-- Assert a Boolean term is true. -/
def assert := @is_generator.assert

/-- Declare a function -/
def declare_fun := @is_generator.declare_fun

/-- Declare a constant with the given name -/
def declare_const := @is_generator.declare_const

/-- Declare a function -/
def define_fun := @is_generator.define_fun

end smt2
