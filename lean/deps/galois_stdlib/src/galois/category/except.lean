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
end
end except
