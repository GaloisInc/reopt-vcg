/-
Provides a decidable_eq instance for buffer.
-/
import data.buffer

namespace buffer

instance {α} [decidable_eq α] : decidable_eq (buffer α) := by tactic.mk_dec_eq_instance

end buffer
