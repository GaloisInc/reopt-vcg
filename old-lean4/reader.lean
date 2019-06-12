namespace ReadMonad
variable {m: Type → Type _}
variable [h:Monad m]
include h

def readN' (rc : m Char) : String → ℕ → m String
| s 0 := pure s
| s (Nat.succ i) := do
  c ← rc,
  readN' (s.push c) i

end ReadMonad

class ReadMonad (m : Type → Type _) extends Monad m, MonadFail m :=
(atEnd {} : m Bool)
(peek {} : m Char)
(skip {} : m PUnit)
(read {} : m Char := seqLeft peek skip)
(readN {} : ℕ → m String := ReadMonad.readN' read "")

def StringReader := EState String Substring

namespace StringReader

section
attribute [reducible] StringReader

protected
def fail {α:Type} : String → StringReader α := throw

protected
def atEnd : StringReader Bool := do
  s ← get,
  pure (s.startPos ≥ s.stopPos)

protected
def peek : StringReader Char := do
  s ← get,
  when (s.startPos + 1 > s.stopPos) (throw "At end of string"),
  pure s.front

protected
def skip : StringReader Unit := do
  s ← get,
  when (s.startPos + 1 > s.stopPos) (throw "At end of string"),
  set (s.drop 1)

protected
def read : StringReader Char := do
  s ← get,
  when (s.startPos + 1 > s.stopPos) (throw "At end of string"),
  set (s.drop 1),
  pure s.front

protected
def readN (n:ℕ) : StringReader String := do
  s ← get,
  when (s.startPos + n > s.stopPos) (throw "At end of string"),
  set (s.drop n),
  pure (s.take n).toString

end

instance : MonadFail StringReader :=
{ fail := @StringReader.fail
}

instance : ReadMonad StringReader :=
{ atEnd := StringReader.atEnd
, peek := StringReader.peek
, skip := StringReader.skip
, read := StringReader.read
, readN := StringReader.readN
}

end StringReader

section readHandle

variable {α : Type}

def readFromString (s : String) (m : StringReader α) : EState.Result String Substring α :=
  m (EState.resultOk.mk () s.toSubstring)

end readHandle
