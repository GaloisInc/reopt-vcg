namespace Char

def isHexDigit (c:Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'f' ∨ 'A' ≤ c ∧ c ≤ 'F' ∨ '0' ≤ c ∧ c ≤ '9'

def hexToNat (c:Char) : Nat :=
  if 'a' ≤ c ∧ c ≤ 'f' then
    c.toNat - 'a'.toNat
  else if 'A' ≤ c ∧ c ≤ 'F' then
    c.toNat - 'A'.toNat
  else
    c.toNat - '0'.toNat


end Char


namespace String

def hexToNat (s : String) : Nat := s.foldl (λ n c, 16*n + c.hexToNat) 0

end String


namespace RBNode
variable {α : Type _}
variable {β : Type _}
variable (lt : α → α → Bool)

def ofList' : RBNode α (λ_, β) → List (α × β) → RBNode α (λ_, β)
| l [] := l
| l ((k,v) :: r) := ofList' (l.insert lt k v) r


def ofList (l:List (α × β)) : RBNode α (λ_, β) := ofList' lt leaf l


section
variable {A:Type _}
variable {B:A → Type _}
variable {σ : Type _}
variable (f : Π(k:A), B k → σ → σ)

def foldRight : RBNode A B → σ → σ
| RBNode.leaf s := s
| (RBNode.node _ l k v r) s := foldRight l (f k v (foldRight r s))

end

end RBNode


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

namespace json

-- Scientific notation (note this does not maintain a normal form for now)
structure Scientific :=
(numerator : Int)
(exponent : Int)

namespace Scientific

def toString (s:Scientific) : String :=
let e := s.exponent
 in toString (s.numerator) ++ (if e == 0 then "" else "E" ++ toString e)

end Scientific

def stringLt (x y : String) : Bool := Decidable.toBool (x < y)

inductive Value
-- It may be better to put an RBMap here.
--| object : RBMap String Value stringLt → Value
| object : RBNode String (λ_, Value)  → Value
--| object : Array (AssocList String Value)  → Value
-- This works of course
--| object : List (String × Value) → Value
| array : Array Value → Value
| string : String → Value
| number : Scientific → Value
| bool : Bool → Value
| null : Value

namespace Value

def true : Value := Value.bool True
def false : Value := Value.bool False

def ofNat (n:ℕ) : Value := Value.number ⟨Int.ofNat n, 0⟩

def ofList (l:List Value) := Value.array (List.toArray l)

def listObj (l:List (String × Value)) : Value := object (RBNode.ofList stringLt l)

def isControl (c:Char) : Bool := c.val ≤ 0x1f ∨ c.val = 0x7f

def utf8Escape' : String → List Char → String
| p [] := p
| p (c::l) :=
  if c.val = 0x22 then
    utf8Escape' (p ++ "\\\"") l
  else if c.val = 0x8 then
    utf8Escape' (p ++ "\\b") l
  else if c.val = 0xc then
    utf8Escape' (p ++ "\\f") l
  else if c = '\n' then
    utf8Escape' (p ++ "\\n") l
  else if c.val = 0xd then
    utf8Escape' (p ++ "\\r") l
  else if c = '\t' then
    utf8Escape' (p ++ "\\t") l
  else if isControl c then
    let v := c.val in
    let s := if v < 0x10 then "000" ++ toString v else "00" ++ toString v in
    utf8Escape' (p ++ "\\u" ++ s) l
  else
    utf8Escape' (p.push c) l

def utf8Escape (l:String) (s:String) : String := (utf8Escape' (l.push '\"') s.data).push '\"'

/-
partial
def toString  : Value → String
| (object m) :=
    let f (s:String) (k:String) (v:Value) : String
           := (if s.isEmpty then "" else s ++ ", ")
           ++ k ++ ": " ++ toString v in
    "{" ++ m.fold f "" ++ "}"
| (array a) := a.iterate "[" (λi v s, s ++ (if i.val = 0 then "" else ", ") ++ toString v) ++ "]"
| (string s) := "\"" ++ utf8Escape s ++ "\""
| (number s) := s.toString
| (bool b)   := if b then "true" else "false"
| null := "null"
-/

partial
def toStringPre  : String → Value → String
| l (object m) :=
    let f (s:Bool × String) (k:String) (v:Value) : Bool × String
           := (False, toStringPre (utf8Escape (if s.fst then s.snd else s.snd ++ ", ") k ++ ": ") v) in
    (m.fold f (True, l ++ "{")).snd ++ "}"
| l (array a) := a.iterate (l ++ "[") (λi v s, toStringPre (s ++ (if i.val = 0 then "" else ", ")) v) ++ "]"
| l (string s) := utf8Escape (l.push '\"') s ++ "\""
| l (number s) := l ++ s.toString
| l (bool b)   := l ++ (if b then "true" else "false")
| l null := l ++ "null"

instance : HasToString Value := ⟨toStringPre ""⟩

section read
variable {m: Type → Type}
variable [h:ReadMonad m]
include h

attribute [instance] monadInhabited

open MonadFail
open ReadMonad

-- This reads a string lit until reaching the trailing quote.
-- The argument is the string so far.
partial
def readStringLit' : String → m String | l := do
  c ← read,
  if c = '\"' then -- Quote
    pure l
  else if c = '\\' then do -- Reverse solidus
    d ← read,
    match d with
    | '\"' := readStringLit' (l.push c)
    | '\\' := readStringLit' (l.push c)
    | '/'  := readStringLit' (l.push c)
    | 'b'  := readStringLit' (l.push '\x08')
    | 'f'  := readStringLit' (l.push '\x0c')
    | 'n'  := readStringLit' (l.push '\n')
    | 'r'  := readStringLit' (l.push '\x0d')
    | 't'  := readStringLit' (l.push '\t')
    | 'u' := do
      n ← readN 4,
      (when (not (n.all Char.isHexDigit)) $ fail ("Expected hex digits, found " ++ repr n)),
      let r := n.hexToNat,
      -- TODO: Consider checking this is not a control character and isValidChar
      readStringLit' (l.push (Char.ofNat r))
    | _   := fail ("Unexpected escape character " ++ repr d)
  else
    readStringLit' (String.singleton c ++ l)

partial
def readStringLit : Unit → m String | () := do
  c ← read,
  if c.isWhitespace then
    readStringLit ()
  else if c = '\"' then
    readStringLit' ""
  else
    fail "Expected start of string literal."

-- This reads a natural number given a nat containing digits read so far.
partial
def readNat' : Nat → m Nat | r := do
  b ← atEnd,
  if b then
    pure r
  else do
    c ← peek,
    if c.isDigit then
      readNat' (10 * r + (c.toNat - '0'.toNat))
    else
      pure r

partial
def readNat : m Nat := do
  c ← read,
  if c = '0' then
    pure 0
  else if c.isDigit then
    readNat' (c.toNat - '0'.toNat)
  else
    fail $ "Expected a digit, found " ++ repr c

-- This reads a natural number, and returns it along with the number of digits read.
partial
def readNatWithDigits' : ℕ → ℕ → m (Nat × Nat) | n r := do
  b ← atEnd,
  if b then
    pure (n,r)
  else do
    c ← peek,
    if c.isDigit then do
      skip,
      readNatWithDigits' (n+1) (10 * r + (c.toNat - '0'.toNat))
    else
      pure (n,r)

-- Read a digit
def readDigit : m ℕ := do
  d ← read,
  (when (not d.isDigit) $ fail "Expected a digit"),
  pure (d.toNat - '0'.toNat)

-- This reads a decimal number "(.yyy)"
def readDecimal (p:Nat) : m Scientific := do
  b ← atEnd,
  if b then
    pure ⟨p,0⟩
  else do
    c ← peek,
    if c = '.' then do
      skip,
      d ← readDigit,
      (n,r) ← readNatWithDigits' 1 (10 * p + d),
      pure ⟨r, - (n:Int)⟩
    else
      pure ⟨p,0⟩

-- Read an optional exponent string of form ([e,E](+/-)nnnn)
def readExponent (n:Scientific) : m Scientific := do
  b ← atEnd,
  if b then
    pure n
  else do
    -- Look ahead for exponent
    c ← peek,
    if c = 'e' ∨ c = 'E' then do
      skip,
      d ← read,
      if d = '+' then do
        e ← readNat,
        pure { n with exponent := n.exponent + e }
      else if d = '-' then do
        e ← readNat,
        pure { n with exponent := n.exponent - e }
      else do
        e ← readNat,
        pure { n with exponent := n.exponent + e }
    else
      pure n

def expect (pre:String) (r:String) : m Unit := do
  e ← readN r.length,
  when (e ≠ r) (fail $ "Expected token " ++ repr (pre ++ r))

partial
def readColon : Unit → m Unit | () := do
  c ← read,
  if c.isWhitespace then do
    readColon ()
  else if c = ':' then
    pure ()
  else
    fail ("Unexpected character: " ++ repr c)

section
variable {α : Type _}
variable {β : α → Type _}

instance inhabited : Inhabited (RBNode α β) := ⟨RBNode.leaf⟩

end

partial
def readBindings' {α} (readVal : m α)
: RBNode String (λ_, α) → m (RBNode String (λ_, α))
| bindings := do
   c ← read,
   if c.isWhitespace then
     readBindings' bindings
   else if c = '}' then
     pure bindings
   else if c = ',' then do
     nm ← readStringLit (),
     readColon (),
     v ← readVal,
     (match RBNode.find stringLt bindings nm with
     | Option.none := pure ()
     | (Option.some _) := fail $ "Name " ++ repr nm ++ " already bound."),
     readBindings' (bindings.insert stringLt nm v)
   else
     fail "Expected field name or '}'"

partial
def readBindings {α} (readVal : m α) : Unit → m (RBNode String (λ_, α))
| bindings := do
   c ← read,
   if c.isWhitespace then
     readBindings ()
   else if c = '}' then
     pure RBNode.leaf
   else if c = '\"' then do
     nm ← readStringLit' "",
     readColon (),
     v ← readVal,
     readBindings' readVal (RBNode.leaf.insert stringLt nm v)
   else
     fail "Expected field name or '}'"


partial
def readArray' {α} (readVal : m α)
: Array α → m (Array α)
| prev := do
   c ← read,
   if c.isWhitespace then
     readArray' prev
   else if c = ']' then
     pure prev
   else do
     v ← readVal,
     readArray' (prev.push v)

instance : Inhabited Value := ⟨Value.null⟩

partial
def readValue' : Unit → m Value | () := do
  c ← ReadMonad.read,
  if c.isWhitespace then
    readValue' ()
  else if c = '\"' then do
    Value.string <$> readStringLit' ""
  else if c = '-' then do -- Negative scientific
    n ← (readNat >>= readDecimal)  >>= readExponent,
    pure (Value.number { n  with numerator := - n.numerator })
  else if c = '0' then do
    n ← readDecimal 0 >>= readExponent,
    pure (Value.number n)
  else if '1' ≤ c ∧ c ≤ '9' then do
    n ← (readNat' (c.toNat - '0'.toNat) >>= readDecimal) >>= readExponent,
    pure (Value.number n)
  else if c = '{' then do
    -- Read object.
    Value.object <$> readBindings (readValue' ()) ()
  else if c = '[' then -- Start of array
    -- Read array
    Value.array <$> readArray' (readValue' ()) Array.empty
  else if c = 't' then
    expect "t" "rue" *> pure Value.true
  else if c = 'f' then
    expect "f" "alse" *> pure Value.false
  else if c = 'n' then
    expect "n" "ull" *> pure Value.null
  else
    fail ("Unexpected character " ++ repr c)

def readValue : m Value := readValue' ()

end read

end Value

end json
