/-
Provides a decidable_eq instance for buffer.
-/
import data.buffer.basic -- from mathlib

import galois.data.array
import galois.data.char
import galois.data.nat

namespace buffer

@[simp]
theorem size_append_array {α} {n : nat} (nz : n > 0)  (x : buffer α) (y : array n α) (j : nat) (j_lt : j < n)
: buffer.size (buffer.append_array nz x y j j_lt) = x.size + j + 1 :=
begin
  revert x,
  induction j,
  case nat.zero {
    intro x,
    cases x,
    simp [append_array, size],
  },
  case nat.succ : j ind {
    intro x,
    cases x with m b,
    simp [append_array, ind],
    simp [size, nat.succ_add, nat.add_succ],
  },
end

/- Size of appending to buffers is sum of their sizes.-/
@[simp]
theorem size_append {α} (x y : buffer α)
: (x ++ y).size = x.size + y.size :=
begin
  cases y with n b,
  cases n,
  case nat.zero { simp [size, append, buffer.append], },
  case nat.succ : n {
    simp [size, append, buffer.append, size_append_array, nat.succ_add],
  }
end

@[simp]
theorem to_list_length {α} (b: buffer α)
: list.length (buffer.to_list b) = b.size :=
begin
  simp only [buffer.to_list, size, array.to_list_length],
end

/-- Replace nil.to_list with empty list. -/
@[simp]
theorem nil_to_list (α:Type _) : (@buffer.nil α).to_list = [] := refl []

/-- Convert read to list read so we can use list lemmas -/
theorem read_to_nth_le {α} (b: buffer α) (i:fin b.size)
: buffer.read b i = list.nth_le b.to_list i.val ((to_list_length b).symm ▸ i.is_lt) :=
begin
  cases b with n a,
  simp only [read, to_list, array.to_list_nth_le', to_array],
end

/-- Empty buffer converted to array is same as array.nil -/
@[simp]
theorem to_array_mk_buffer {α} : to_array mk_buffer = @array.nil α :=
begin
  apply array.ext,
  intro i,
  have h : false := fin.elim0 i,
  contradiction,
end

/-- Converting list to bufer and back is round trip. -/
theorem to_list_to_buffer {α} (l:list α) : buffer.to_list (list.to_buffer l) = l :=
begin
  unfold list.to_buffer,
  simp only [to_list_append_list],
  simp only [to_list, to_array_mk_buffer, array.to_list_nil, list.nil_append],
end

/- Simplify functions calling through as_string -/
theorem to_char_buffer_as_string (l:list char)
: l.as_string.to_char_buffer = l.to_buffer := eq.refl l.to_buffer

@[simp]
theorem size_push_back {α} (b:buffer α) (c:α)
: (buffer.push_back b c).size = b.size + 1 :=
begin
  cases b,
  trivial,
end

@[simp]
theorem size_append_list {α} (b:buffer α) (l:list α)
: (buffer.append_list b l).size = l.length + b.size :=
begin
  revert b,
  induction l,
  case list.nil {
    intro b,
    simp [buffer.append_list, nat.zero_add],
  },
  case list.cons : x r ind {
    intro b,
    simp only [buffer.append_list, ind, size_push_back, list.length_cons,
               nat.add_succ, nat.add_zero, nat.succ_add],
  },
end

/- Prove definition of reading from concatenation of two buffers. -/
theorem read_append_array {α} {n:ℕ} (nz : n > 0) (x : buffer α) (b : array n α) (j:ℕ) (j_lt : j < n)
   (i : fin (append_array nz x b j j_lt).size)
: read (append_array nz x b j j_lt) i =
  if h : i.val < x.size then
    x.read ⟨i.val, h⟩
  else
    let q : n + (i.val - x.size) - (j + 1)  < n :=
      begin
        cases i with i i_lt,
        let nz_lt : 0 < n := nz,
        simp only [nat.sub_lt_to_add, nz_lt, or_true, and_true],
        apply nat.add_lt_add_left,
        have x_le := le_of_not_lt h,
        simp [nat.sub_lt_to_add, x_le],
        simp [size_append_array] at i_lt,
        exact i_lt,
      end in
    array.read b ⟨n + (i.val - x.size) - (j + 1), q⟩ :=
begin
  revert x,
  induction j,
  case nat.zero {
    intros x i,
    cases i with i i_lt,
    cases x with m a,
    dsimp [append_array, read, size],
    simp [array.read_push_back_lt_iff],
    cases (decide (i < m)),
    case decidable.is_true : lt {
      simp [lt],
    },
    case decidable.is_false : not_lt {
      simp [not_lt],
      dsimp [append_array, size] at i_lt,
      have p : i ≤ m := nat.le_of_lt_succ i_lt,
      have q : i-m=0 := nat.sub_eq_zero_of_le p,
      simp [q],
    },
  },
  case nat.succ : j ind {
    intros x i,
    cases i with i i_outer_lt,
    cases x with m a,
    dsimp [append_array, size],
    simp [ind],
    dsimp [size],
    cases nat.lt_trichotomy i m,
    case or.inl : i_lt {
      have i_lt_m_p_1 : i < m + 1 := nat.lt_succ_of_lt i_lt,
      simp [i_lt, i_lt_m_p_1, read, array.read_push_back_lt_iff],
    },
    case or.inr : i_geq {
      cases i_geq,
      case or.inl : i_eq {
        have i_lt_m_p_1 : i < m + 1, { simp [i_eq, nat.zero_lt_succ], },
        simp [i_lt_m_p_1, i_eq, read, array.read_push_back_lt_iff],
        apply (congr_arg (array.read b)),
        apply fin.eq_of_veq,
        simp [nat.succ_add, nat.add_succ, nat.sub_sub],
      },
      case or.inr : i_gt {
        have not_i_lt_m : ¬ (i < m) := not_lt_of_lt i_gt,
        have not_i_lt_m_p_1 : ¬ (i < m + 1), {
          apply not_lt_of_le,
          exact i_gt,
        },
        simp [not_i_lt_m, not_i_lt_m_p_1],
        apply (congr_arg (array.read b)),
        apply fin.eq_of_veq,
        have not_i_m_zero : ¬(i - m = 0), {
          intro eq_zero,
          have not_i_gt := not_lt_of_ge (nat.le_of_sub_eq_zero eq_zero),
          exact (not_i_gt i_gt),
        },
        simp [fin.val, nat.succ_add, nat.add_succ, nat.sub_succ
             , nat.add_pred, nat.pred_sub, not_i_m_zero],
      },
    },
  },
end

/-- Proof needed for starting theorem about read of append. -/
theorem read_append.pr1 {α} (x y : buffer α) (i : fin ((x++y).size)) (h : ¬(i.val < x.size ))
: i.val - buffer.size x < buffer.size y :=
begin
  have q : buffer.size x ≤ i.val := le_of_not_lt h,
  simp [nat.sub_lt_left_iff_lt_add q],
  exact trans_rel_left _ i.is_lt (size_append _ _),
end

/- Prove definition of reading from concatenation of two buffers. -/
theorem read_append {α} (x y : buffer α) (i : fin ((x++y).size))
: (x ++ y).read i =
  if h : i.val < x.size then
    x.read ⟨i.val, h⟩
  else
    y.read ⟨i.val - x.size, read_append.pr1 x y i h⟩ :=
begin
  cases y with n b,
  cases n,
  case nat.zero {
    cases i with i i_lt,
    dsimp [has_append.append, buffer.append] at i_lt,
    -- Simplify left-hand side
    dsimp [has_append.append, buffer.append],
    -- Simplify right-hand side
    simp [i_lt],
  },
  case nat.succ : n {
    cases i with i i_lt,
    dsimp [has_append.append, buffer.append],
    simp [read_append_array ],
    dsimp [fin.val],
    cases decide (i < size x),
    case decidable.is_true : i_lt { simp [i_lt], },
    case decidable.is_false : not_i_lt {
      simp [not_i_lt, read],
      apply congr_arg (array.read b),
      exact fin.eq_of_veq (eq.refl _),
    },
  },
end

/- Lexicographic reflexive ordering of buffers -/
protected
def le {α} [h:linear_order α] : buffer α → buffer α → Prop
| ⟨m,a⟩ ⟨n,b⟩ := array.lex_le a b

instance {α} [h:linear_order α] : has_le (buffer α) := ⟨buffer.le⟩

instance decidable_le {α} [h:linear_order α] [r:decidable_rel (h.lt)]
: Π(x y : buffer α), decidable (x ≤ y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_le.le, buffer.le],
  apply_instance,
end

/- Lexicographic strict ordering of buffers -/
protected
def lt {α} [h:linear_order α] : buffer α → buffer α → Prop
| ⟨m,a⟩ ⟨n,b⟩ := array.lex_lt a b

instance {α} [h:linear_order α] : has_lt (buffer α) := ⟨buffer.lt⟩

instance decidable_lt {α} [h:linear_order α] [r:decidable_rel (h.lt)]
: Π(x y : buffer α), decidable (x < y)
| ⟨m,a⟩ ⟨n,b⟩ :=
begin
  simp [has_lt.lt, buffer.lt],
  apply_instance,
end

/- Take a specific range of elements out of a buffer. -/
def slice {α} : Π(b : buffer α) (s e : ℕ) (s_le_e : s ≤ e), buffer α
| ⟨n, a⟩ s e s_le_e :=
  if e_le_n : e ≤ n then
    ⟨e - s, a.slice s e s_le_e e_le_n⟩
  else if s_le_n : s ≤ n then
    ⟨n - s, a.slice s n s_le_n (nat.le_refl _)⟩
  else
    ⟨0, array.nil⟩

/- Take a specific range of elements out of a buffer. -/
@[simp]
theorem size_slice {α} (b : buffer α) (s e : ℕ) (s_le_e : s ≤ e) :
  size (slice b s e s_le_e) = min e b.size - s :=
begin
  cases b with n a,
  cases (decide (e ≤ n)),
  case decidable.is_true : e_le_n {
    simp [slice, e_le_n, size, min_eq_left],
  },
  case decidable.is_false : not_e_le_n {
    have n_le_e : n ≤ e := le_of_not_ge not_e_le_n,
    simp [slice, not_e_le_n, size, min_eq_right n_le_e],
    cases (decide (s ≤ n)),
    case decidable.is_true : s_le_n {
      simp [s_le_n, n_le_e, min_eq_right],
    },
    case decidable.is_false : not_s_le_n {
      simp [not_s_le_n],
      have n_le_s : n ≤ s := le_of_not_ge not_s_le_n,
      apply (eq.symm (nat.sub_eq_zero_of_le n_le_s)),
    },
  },
end

/-- Introduce a non-dependent function for reading. -/
def try_read {α} (b:buffer α) (i:ℕ) : option α :=
  if i_lt : i < b.size then
    option.some (b.read ⟨i, i_lt⟩)
  else
    option.none

/- Simplify some (read ...) -/
theorem some_read_is_try_read {α} (x:buffer α) (i:fin x.size)
: option.some (read x i) = try_read x i.val :=
begin
  simp [try_read, i.is_lt],
end

/-- Lemma to force simplification of size, but only when buffer uses explicit constructor. -/
theorem size_ctor {α} (m:ℕ) (a:array m α) : size (⟨m,a⟩) = m := by trivial

/- Lemma that uses the index to a slice to show it is bounded by size of buffer. -/
theorem slice_index_bound {α} {b:buffer α} {s e :ℕ} {pr : s ≤ e}
   (i:fin (size (slice b s e pr)))
: s + i.val < b.size :=
begin
  cases b with m a,
  cases i with i i_lt,
  simp [size_slice, nat.lt_sub_right_iff_add_lt] at i_lt,
  exact calc s + i < min e m : i_lt
               ... ≤ m : min_le_right _ _,
end

/- Simplify reading from slice -/
theorem read_slice {α} {b:buffer α} {s e :ℕ} {s_le_e : s ≤ e} (i:fin (size (slice b s e s_le_e)))
: read (slice b s e s_le_e) i = read b ⟨s + i.val, slice_index_bound i⟩ :=
begin
  cases b with m a,
  cases i with i i_lt,
  apply option.some.inj,
  simp [some_read_is_try_read],

  cases (decide (e ≤ m)),
  case decidable.is_true : e_le_m {
    simp [size_slice, size_ctor, min_eq_left e_le_m] at i_lt,
    -- Reduce to array slice
    simp [slice, e_le_m, read],
    -- Simplify away try_read
    have s_i_lt_m : s+i < m :=
      calc s + i < e : nat.add_lt_of_lt_sub_left i_lt
                   ... ≤ m : e_le_m,
    simp [try_read, size_ctor, i_lt, s_i_lt_m, read],
    -- Simplify array theorem
    simp [array.read_slice],
    apply congr_arg _ (fin.eq_of_veq (eq.refl _)),
  },
  case decidable.is_false : not_e_le_m {
    have m_le_e : m ≤ e := le_of_not_ge not_e_le_m,
    simp [size_slice, size_ctor, min_eq_right m_le_e] at i_lt,
    simp [slice, not_e_le_m, read],
    cases (decide (s ≤ m)),
    case decidable.is_true : s_le_m {
      -- Reduce to array slice
      simp [s_le_m],
      -- Simplify away try_read
      have s_i_lt_m : s+i < m := nat.add_lt_of_lt_sub_left i_lt,
      simp [try_read, size_ctor, i_lt, s_i_lt_m, read],
      -- Simplify array theorem
      simp [array.read_slice],
      apply congr_arg _ (fin.eq_of_veq (eq.refl _)),
    },
    case decidable.is_false : not_s_le_m {
      -- Show i must be less than zero.
      have m_le_s : m ≤ s := le_of_not_ge not_s_le_m,
      have m_sub_s_eq_0 := nat.sub_eq_zero_of_le m_le_s,
      simp [m_sub_s_eq_0] at i_lt,
      -- Use i_lt : i < 0 to discharge proof
      exact (false.elim (nat.not_lt_zero _ i_lt)),
    },
  },
end

end buffer

namespace string

/- Simplify functions calling through as_string -/
theorem to_char_buffer_as_string (l:list char)
: to_char_buffer (list.as_string l) = list.to_buffer l := eq.refl l.to_buffer

theorem to_char_buffer_buffer_to_string (b:char_buffer) : to_char_buffer (buffer.to_string b) = b :=
begin
  apply buffer.ext,
  simp [buffer.to_string],
  simp [to_char_buffer_as_string],
  simp [buffer.to_list_to_buffer],
  simp [buffer.to_list],
end

end string
