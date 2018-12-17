/-
This provides a few missing definitions to the except monad
-/

namespace except
section
  universes u v
  parameter {ε : Type u}

  protected def catch {α : Type v} (ma : except ε α) (f : ε → except ε α) : except ε α :=
  match ma with
  | (except.error err) := f err
  | (except.ok v) := except.ok v
  end

  protected def throw {α : Type v} :  ε → except ε α := except.error

  instance : monad_except ε (except ε) :=
  { throw := @except.throw
  , catch := @except.catch
  }
end
end except
