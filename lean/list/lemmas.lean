/-
Copyright (c) 2018 Galois. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Additional lemmas for lists.

This is a work-in-progress, and contains additions to other theories.
-/

import tactic.find
import ..tactic

open nat

section reverse
  universes u

  lemma reverse_core_step {α : Type u} (x : α) (xs : list α) (ys : list α)
  : list.reverse_core (x::ys) xs = list.reverse ys ++ x::xs :=
  begin
    induction ys with y ys ih generalizing x xs,
    case list.nil
    { simp [list.reverse_core], },
    case list.cons
    { rw [ih],
      simp [list.reverse_core],
      rw [←ih],
      simp [list.reverse_core],
    },
  end

end reverse
