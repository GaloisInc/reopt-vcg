/-
This defines an interface for reading characters with one-character lookahead.
-/
-- import data.buffer
-- import system.io
-- import galois.data.list

------------------------------------------------------------------------
-- is_parse_error

class is_parse_error (ε : Type _) :=
(end_of_input {} : ε)

namespace is_parse_error

instance string_is_parse_error : is_parse_error String :=
{ end_of_input := "end of input" }

end is_parse_error

------------------------------------------------------------------------
-- char_reader

/-- A class for a monad that can read characters with a one-byte lookahead. -/
class {u v} char_reader (ε : outParam (Type u)) (m : Type → Type v)
  extends is_parse_error ε, Monad m, MonadExcept ε m :=
(at_end {} : m Bool)
(peek_char {} : m (Option Char))
-- Drop the next character
(consume_char {} : m Unit)
(read_char {} : m Char)

@[reducible]
def char_buffer := ByteArray

namespace char_reader

section read_while

variable {m : Type → Type}
variable [char_reader String m]
variable (p : Char → Prop)
variable [DecidablePred p]

/--  Append characters to buffer while not at end of file and the predicate is true. -/
def read_while_f :
  Π(n:ℕ)
   (f : Π(j:ℕ), j < n → char_buffer → m char_buffer),
   char_buffer → m char_buffer
| 0 f prev := do
  throw "Maximum length exceeded"
| (Nat.succ i) f prev := do
  mc ← peek_char,
  match mc with
  | Option.none := pure prev
  | Option.some c :=
     if p c then do
       consume_char, f i (Nat.ltSuccSelf _) (prev.push (UInt8.ofNat c.toNat))
     else
       pure prev


/-- @read_append_while n c@ reads up to @n@-characters satisfying @p@ and appends them to @c@. -/
def read_append_while : ℕ → char_buffer → m char_buffer := do
  well_founded.fix nat.lt_wf read_while_f

/-- @read_append_while n c@ reads up to @n@-characters satisfying @p@ and appends them to @c@. -/
def read_while (max_count:ℕ) : m char_buffer := do
  read_append_while max_count buffer.nil

end read_while

/-- Read whitespace characters until a newline is encountered, then consume the newline. -/
def read_to_newline {m} [char_reader string m] : ℕ → m unit
| nat.zero := throw "out of gas"
| (nat.succ n) := do
  c ← read_char,
  if c = '\n' then
    pure ()
  else if c.is_whitespace then
    read_to_newline n
  else
    throw $ "Unexpected character at end of expression " ++ c.to_string

/-- Read up to given number of characters to reach end of file. -/
def read_to_end {m} [char_reader string m] : ℕ → m unit
| nat.zero := throw "out of gas"
| (nat.succ n) := do
  b ← at_end,
  if b then
    pure ()
  else
    consume_char, read_to_end n

------------------------------------------------------------------------
-- handle_char_reader

/-- A char_reader that reads from a handle. -/
def handle_char_reader (ε:Type) := except_t ε (reader_t io.handle (state_t (option char) io))

namespace handle_char_reader
section

parameter (ε : Type)

local attribute [reducible] handle_char_reader

instance is_monad : monad (handle_char_reader ε) := by apply_instance

instance has_monad_lift : has_monad_lift io (handle_char_reader ε) :=
{ monad_lift := λ_, monad_lift }

instance is_monad_except : monad_except ε (handle_char_reader ε) := by apply_instance

end

/- This uses the handle_char_reader to parse output. -/
protected
def read {ε} {α} (h:io.handle) (mc : option char) (m:handle_char_reader ε α)
: io (except ε α × option char) := do
  ((m.run).run h).run mc

section

parameter {ε : Type}

local attribute [reducible] handle_char_reader

/-- Return true if the handle is at the end of the stream. -/
protected
def at_end [is_parse_error ε] : handle_char_reader ε bool := do
  mc ← get,
  match mc with
  | option.some c := pure ff
  | option.none := do
     h ← read,
     monad_lift (io.fs.is_eof h)
  end

/-- Attempt to read character from handle. -/
protected
def peek_char [is_parse_error ε] : handle_char_reader ε (option char) := do
  mc ← get,
  match mc with
  | option.some c := pure c
  | option.none := do
    h ← read,
    b ← monad_lift (io.fs.read h 1),
    if h : b.size = 1 then do
      let c := b.read ⟨0, h.symm ▸ zero_lt_one⟩,
      put (option.some c) $> c
    else
      pure option.none
  end

protected
def get_char [is_parse_error ε] : handle_char_reader ε char := do
  mc ← get,
  match mc with
  | (option.some c) := put option.none $> c
  | option.none := do
    h ← read,
    b ← monad_lift (io.fs.read h 1),
    if h : b.size = 1 then
      pure (b.read ⟨0, h.symm ▸ zero_lt_one⟩)
    else
      throw is_parse_error.end_of_input
  end

protected
def consume_char [is_parse_error ε] : handle_char_reader ε unit := get_char $> ()

end

instance is_char_reader (ε:Type) [is_parse_error ε] : char_reader ε (handle_char_reader ε) :=
{ at_end       := handle_char_reader.at_end
, peek_char    := handle_char_reader.peek_char
, consume_char := handle_char_reader.consume_char
, read_char    := handle_char_reader.get_char
}

/-- For some reason, instance resolution fails below without this instance. -/
def string_is_char_reader : char_reader string (handle_char_reader string) :=
  @handle_char_reader.is_char_reader string is_parse_error.string_is_parse_error

local attribute [instance] string_is_char_reader

end handle_char_reader

def read_from_handle {α} (h:io.handle) (m:handle_char_reader string α)
: io (except string α) := do
  (e, mc) ← handle_char_reader.read h option.none m,
  match mc with
  | option.none := pure e
  | (option.some _) := pure (except.error "")
  end


------------------------------------------------------------------------
-- string_char_reader

/-- Character reader that rads from a list of characters in memory. -/
def string_char_reader (ε:Type) := except_t ε (state (list char))

namespace string_char_reader
section

parameter (ε : Type)

local attribute [reducible] string_char_reader

instance is_monad : monad (string_char_reader ε) := by apply_instance
instance is_monad_except : monad_except ε (string_char_reader ε) := by apply_instance

end

/- This uses the string_char_reader to parse output. -/
protected
def read {ε} {α} (s:list char) (m:string_char_reader ε α)
: (except ε α × list char) := (m.run).run s

section

variable {ε : Type}

local attribute [reducible] string_char_reader

/-- Return true if the handle is at the end of the stream. -/
protected
def at_end [is_parse_error ε] : string_char_reader ε bool := do
  (λ(l:list char), l.is_empty) <$> get

protected
def peek_char [is_parse_error ε] : string_char_reader ε (option char) := do
  s ← get,
  match s with
  | [] := pure option.none
  | (c::s) := pure (option.some c)
  end

/-- Read the next character. -/
protected
def get_char [is_parse_error ε] : string_char_reader ε char := do
  s ← get,
  match s with
  | [] := throw is_parse_error.end_of_input
  | (c::s) := put s $> c
  end

/-- Read the next character, but do not return it. -/
protected
def consume_char [is_parse_error ε] : string_char_reader ε unit := string_char_reader.get_char $> ()

end

instance is_char_reader (ε:Type) [is_parse_error ε] : char_reader ε (string_char_reader ε) :=
{ at_end       := string_char_reader.at_end
, peek_char    := string_char_reader.peek_char
, consume_char := string_char_reader.consume_char
, read_char    := string_char_reader.get_char
}

/-- For some reason, instance resolution fails below without this instance. -/
instance string_is_char_reader : char_reader string (string_char_reader string) :=
  @string_char_reader.is_char_reader string is_parse_error.string_is_parse_error

end string_char_reader

/-- Parse input from a string and ensure that all characters are read. -/
def read_from_string {α} (s:string) (m:string_char_reader string α)
: except string α := do
  let r := string_char_reader.read s.to_list m,
  v ← r.1,
  when (¬(r.2.is_empty))
    (except.error ("Parsed terminated prematurely - remaining input: " ++ r.2.as_string.quote)),
  pure v

end char_reader
