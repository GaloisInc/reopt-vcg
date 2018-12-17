import data.buffer
import system.io
import galois.data.list

------------------------------------------------------------------------
-- is_parse_error

class is_parse_error (ε : Type _) :=
(end_of_input {} : ε)

namespace is_parse_error

instance string_is_parse_error : is_parse_error string :=
{ end_of_input := "end of input" }

end is_parse_error

------------------------------------------------------------------------
-- char_reader

/-- A class for a monad that can read characters with a one-byte lookahead. -/
class {u v} char_reader (ε : out_param (Type u)) (m : Type → Type v)
  extends is_parse_error ε, monad m, monad_except ε m :=
(at_end {} : m bool)
(peek_char {} : m (option char))
-- Drop the next character
(consume_char {} : m unit)
(read_char {} : m char)

namespace char_reader

section read_while

parameter {m : Type → Type}
parameter [char_reader string m]
parameter (p : char → Prop)
parameter [decidable_pred p]

/--  Append characters to buffer while not at end of file and the predicate is true. -/
def read_while_f :
  Π(n:ℕ)
   (f : Π(j:ℕ), j < n → char_buffer → m char_buffer),
   char_buffer → m char_buffer
| 0 f prev := do
  throw "Maximum length exceeded"
| (nat.succ i) f prev := do
  mc ← peek_char,
  match mc with
  | option.none := pure prev
  | option.some c :=
     if p c then do
       consume_char, f i (nat.lt_succ_self _) (prev.push_back c)
     else
       pure prev
  end

/-- @read_append_while n c@ reads up to @n@-characters satisfying @p@ and appends them to @c@. -/
def read_append_while : ℕ → char_buffer → m char_buffer := do
  well_founded.fix nat.lt_wf read_while_f

end read_while

/-- Read to newline -/
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

end char_reader

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

def read_to_newline {α} (h:io.handle) (m:handle_char_reader string α)
: io (except string α) := do
  (e, mc) ← handle_char_reader.read h option.none (m <* char_reader.read_to_newline (2^64)),
  match mc with
  | option.none := pure e
  | (option.some _) := pure (except.error "")
  end

end handle_char_reader

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
def read {ε} {α} (s:string) (m:string_char_reader ε α)
: (except ε α × string) := do
  let (r,t) := ((m.run).run s.to_list) in
  (r, t.as_string)

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

protected
def get_char [is_parse_error ε] : string_char_reader ε char := do
  s ← get,
  match s with
  | [] := throw is_parse_error.end_of_input
  | (c::s) := put s $> c
  end

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
def string_is_char_reader : char_reader string (string_char_reader string) :=
  @string_char_reader.is_char_reader string is_parse_error.string_is_parse_error

local attribute [instance] string_is_char_reader

def read_to_end {α} (s:string) (m:string_char_reader string α)
: except string α := (string_char_reader.read s m).1

end string_char_reader
