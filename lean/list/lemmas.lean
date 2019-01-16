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
  : list.reverse_core (x::ys) xs = list.reverse_core ys [] ++ x::xs :=
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

  lemma reverse_length_nil {α : Type u} (xs : list α)
  : list.length (list.reverse_core xs list.nil) = list.length xs :=
  begin
    induction xs with x xs ih,
    case list.nil
    { simp [list.reverse_core], },
    case list.cons
    { simp [reverse_core_step],
      rw ih,
    },
  end

  @[simp]
  lemma length_reverse {α : Type u} {x : list α} : list.length (list.reverse x) = list.length x :=
    begin
      simp [list.reverse],
      apply reverse_length_nil,
    end

  lemma reverse_step (α : Type u) (x : α) (ys : list α)
  : list.reverse (x :: ys) = list.reverse ys ++ [x] :=
  begin
    induction ys with y ys ih,
    case list.nil
    { simp [list.reverse, list.reverse_core] },
    case list.cons
    { simp [list.reverse],
      rw reverse_core_step,
    },
  end

end reverse
