/-
An environment (i.e., type/sort context) for SMT terms/defs.

Copyright (c) 2020 Galois Inc. All rights reserved.
-/
import SmtLib.Syntax


------------------------------------------------------------
-- Generic functional map helpers/theorems

def upd.{u, v} {α : Type u} [DecidableEq α] {β: α -> Type v} (f : forall v, β v) (k : α) (v : β k) : forall v, β v :=       
  fun k' => if H : k = k' then cast (congrArg β H) v else f k'

namespace upd


universes u v
variables {α : Type u} [DecidableEq α] {β: α -> Type v}

theorem atKey (f : forall v, β v) (k : α)  (v : β k) : (upd f k v) k = v :=
  difPos rfl


theorem atOtherKey {k k'} (f : forall v, β v) (v : β k) (pf : k ≠ k') : (upd f k v) k' = f k' :=
  difNeg pf       


end upd


def updMap {α β : Type} [DecidableEq α] (f : α -> Option β) (k : α) (v : β) :  α -> Option β :=
  upd f k (some v)

namespace updMap

def noneSomeNEqKey {α β : Type} [DecidableEq α] (f : α -> Option β) (x y : α) (xPf : f x = none) {v : β} (yPf : f y = some v) : x ≠ y :=
λ h =>
  let yPf' : f y = none := h ▸ xPf;
  let absurd : none = some v := Eq.trans yPf'.symm yPf;
  Option.noConfusion absurd

end updMap


------------------------------------------------------------
-- Env (typing context) for SMT terms


namespace Smt

namespace Raw

def Env := Symbol -> Option ConstSort

namespace Env

@[reducible]
def empty : Env := λ _ => none

@[reducible]
def extend (e : Env) (x : Symbol) (cs : ConstSort) :  Env :=
  upd e x (some cs)

@[reducible]
def extendMany (e : Env) (entries : List (Sigma SortedVar)) : Env :=
  entries.foldr (λ p e' => updMap e' p.snd.var (ConstSort.base p.fst)) e


end Env


end Raw

end Smt
