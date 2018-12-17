/-
This provides a few missing definitions to the except monad
-/

namespace except

section
  universes u v w
  parameter {ε : Type u}


  /-- Polymorphic version of except.map -/
  protected def map_poly {α : Type v} {β : Type w} (f : α → β) : except ε α → except ε β
  | (error err) := error err
  | (ok v) := ok $ f v

  /-- Run a computation.  If it throws an exception, then run handler -/
  protected def catch {α : Type v} (ma : except ε α) (h : ε → except ε α) : except ε α :=
  match ma with
  | (error err) := h err
  | (ok v) := ok v
  end

  /-- Throw an exception -/
  protected def throw {α : Type v} :  ε → except ε α := except.error

  instance : monad_except ε (except ε) :=
  { throw := @except.throw
  , catch := @except.catch
  }

  protected def to_repr {ε} {α} [has_repr ε] [has_repr α] : except ε α → string
  | (ok a)    := "(ok " ++ repr a ++ ")"
  | (error e) := "(error " ++ repr e ++ ")"

  instance {ε} {α} [has_repr ε] [has_repr α] : has_repr (except ε α) :=
  { repr := except.to_repr }

end
end except

namespace except_t

instance is_monad_state {s : Type _} {m : Type _ → Type _} {ε : Type _} [functor m] [monad_state s m]
: monad_state s (except_t ε m) :=
{ lift := λ_ f, ⟨except.ok <$> monad_state.lift f⟩
}

end except_t
