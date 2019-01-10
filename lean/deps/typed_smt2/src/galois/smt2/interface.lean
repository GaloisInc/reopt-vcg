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

export is_generator (assert)
export is_generator (declare_fun)
export is_generator (declare_const)
export is_generator (define_fun)

end smt2
