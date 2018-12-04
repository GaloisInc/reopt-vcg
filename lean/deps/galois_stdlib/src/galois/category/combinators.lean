/-
This defines a few combinators for monads that aren't in the standard library.
-/

universes u v

/-- `pwhen c a` executes `a` when `c` is true; polymorphic version of `when` -/
def pwhen {m : Type u → Type v} [monad m] (c : Prop) [h : decidable c] (t : m punit) : m punit :=
  ite c t (pure punit.star)

/-- `punless c a` executes `a` when `c` is false. -/
def punless {m : Type u → Type v} [monad m] (c : Prop) [h : decidable c] (f : m punit) : m punit :=
  ite c (pure punit.star) f
