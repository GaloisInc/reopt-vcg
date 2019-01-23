import data.buffer

import .basic
import .repr_lemmas

namespace nat

section rendering

def to_digits_buffer.f {base : ℕ} (base_pos : base > 1)
     (n:ℕ) (rec : Π(m:ℕ), m < n → buffer ℕ → buffer ℕ) (prev:buffer ℕ) : buffer ℕ :=
  if h : n < base then
    prev.push_back n
   else
     let n_pos : n > 0 :=
          calc n ≥ base : le_of_not_gt h
            ...  > 1    : base_pos
            ...  > 0    : zero_lt_succ 0 in
     rec (nat.div n base) (div_lt_self n_pos base_pos) (prev.push_back (nat.mod n base))

/--
This is an operation for converting natural numbers into a buffer of naturals.

The standard prelude defines a similiar function nat.to_digits, but it's runtime
is linear with respect to unary size of the number.

This function is primarily useful for bases other than 10, as `repr n` is
efficient in Lean 3, but there is no efficient way to support other bases.
-/
def to_digits_buffer (base : ℕ) (base_pos : base > 1) (n:ℕ) : buffer ℕ :=
  well_founded.fix lt_wf (to_digits_buffer.f base_pos) n buffer.nil

end rendering

end nat
