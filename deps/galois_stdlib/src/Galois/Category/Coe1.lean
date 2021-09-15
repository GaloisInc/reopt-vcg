universe u v w

-- This defines a class for "parameterized" coercisions in which we
-- want to allow coercising `f tp` to some `g tp` while preserving the
-- type `tp`.  This allows coercing even when `tp` contains meta variables,
-- and using unification across the coercision.
class has_coe1 {α:Sort w} (f : α → Sort u) (g : α → Sort v) :=
 (coe : ∀{a : α}, f a → g a)

namespace has_coe1

instance refl (α:Sort w) (f : α → Sort u) : has_coe1 f f :=
 ⟨fun f => f⟩

end has_coe1

def coe1 {α:Type u} {f g : α → Type u} [h:has_coe1 f g] {a:α} (x : f a) : g a :=
  has_coe1.coe x
