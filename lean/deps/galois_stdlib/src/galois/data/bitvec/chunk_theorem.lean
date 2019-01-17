/- This is code intended for chunking/splicing code that will be revisited later. -/
import .basic

namespace bitvec
open nat

  -- splits a bitvector into {n .. m} {m - 1 .. 0} sub bitvectors
  def split_at {n : ℕ} (m : ℕ) (x : bitvec (n + m)) : bitvec n × bitvec m := -- upper × lower
      ⟨ trunc n (bitvec.cong (nat.add_comm _ _) (ushr x m)), trunc m x ⟩

  lemma split_at_snd {n : ℕ} (m : ℕ) (x : bitvec (n+m)): (split_at m x).snd.to_nat < 2 ^ m :=
    begin
      simp [split_at, trunc],
      apply nat.lt_of_lt_of_le,
      { apply mod_lt, apply nat.pos_pow_of_pos, exact (of_as_true trivial) },
      { apply pow_le_pow_of_le_right,
        { exact (of_as_true trivial) },
        { refl }
      }
    end

  lemma trunc_add_ushr {n m : ℕ} (x : bitvec (n + m))
  : (trunc m x).to_nat + (trunc n (bitvec.cong (nat.add_comm _ _) (ushr x m))).to_nat * 2 ^ m = x.to_nat :=
  begin
    simp [ trunc, ushr, bitvec.of_nat, shiftr_eq_div_pow, cong_val],
    have : x.to_nat / 2 ^ m < 2 ^ (n + m),
    { apply div_pow_mono x.property, },
    rw mod_eq_of_lt this,
    rw (pow_mod_superfluous' x.property),
    { rw mul_comm, apply mod_add_div }
  end

  lemma split_at_append_ident {n : ℕ} (m : ℕ) (x : bitvec (n + m))
  : append (split_at m x).fst (split_at m x).snd = x :=
  begin
    apply bitvec.intro,
    simp [append, split_at],
    apply trunc_add_ushr
  end

  def chunks : Π(n :ℕ) (m : ℕ), bitvec (m * n) → list (bitvec m)
    | 0             _ _  := []
    | (nat.succ n)  m bv :=
      let v := bitvec.split_at m bv
      in  v.snd :: chunks n m v.fst

  @[simp]
  lemma chunks_nil {m:ℕ} {x: bitvec (m * 0) }: chunks _ m x = [] :=
    by unfold chunks

  @[simp]
  lemma chunks_length {n m : ℕ} {x: bitvec (m * n)} : list.length (chunks n m x) = n :=
  begin
    induction n with n p,
    case nat.zero
    { unfold chunks, simp },
    case nat.succ
    { simp [chunks, p],
    },
  end

  @[simp]
  lemma chunks_length_mul {n m : ℕ} {x: bitvec (m * n)}
  : m * list.length (chunks n m x) = m * n
  := by simp

  def concat : Π{n : ℕ}(input: list (bitvec n)), bitvec (n * input.length)
    | _ []      := 0
    | n (x::xs) := append (concat xs) x

  @[simp]
  lemma concat_nil_zero {n:ℕ} : concat ([]: list (bitvec n)) = (0 : bitvec 0) :=
  begin
    simp [concat], refl,
  end

  @[simp]
  lemma concat_step {n:ℕ} (x: bitvec n) (xs: list (bitvec n))
  : concat (x::xs) = append (concat xs) x :=
  begin
    simp [concat],
  end

  @[simp]
  lemma chunks_concat_zero {n:ℕ} (x: bitvec (0 * n))
  : concat (chunks n 0 x) = 0 :=
  begin
    induction n with n ih,
    case nat.zero
    { rw [chunks, concat] },
    case nat.succ
    { rw [chunks, concat],
      apply bitvec.intro,
      rw ih,
      simp [cong_val, append, split_at, trunc, bitvec.of_nat],
      refl
    },
  end

  lemma chunks_concat_eq {n m:ℕ} (x: bitvec (m * n))
  : concat (chunks n m x) = bitvec.cong (eq.symm chunks_length_mul) x :=
  begin
    apply bitvec.intro,
    simp [cong_val],
    induction n with n p,
    case nat.zero
    { simp [cong_val], },
    case nat.succ
    { rw [chunks, concat, split_at, append],
      simp [p, cong_val],
      apply trunc_add_ushr,
    },
  end

  def chunks_nat : Π(n :ℕ) (m : ℕ), ℕ → list (bitvec m)
  | 0            _ _ := []
  | (nat.succ n) m v := (bitvec.of_nat m (nat.shiftr v (n*m)) :: chunks_nat n m v)

  @[simp]
  lemma chunks_nat_base {m:ℕ} (v:ℕ)
    : chunks_nat 0 m v = [] :=
    by simp [chunks_nat]

  @[simp]
  lemma chunks_nat_step {n m :ℕ} (v : ℕ)
    : chunks_nat (succ n) m v =
        (bitvec.of_nat m (nat.shiftr v (n*m)) :: chunks_nat n m v) :=
    by simp [chunks_nat]

  @[simp]
  lemma chunks_nat_length {n m : ℕ} (v : ℕ)
    : list.length (chunks_nat n m v) = n :=
    begin
      induction n with n ih,
      case nat.zero
      { simp, },
      case nat.succ
      { simp [chunks_nat_step], rw [ih, ←add_one, add_comm], },
    end

  def chunks' (n m :ℕ) (v:bitvec (m * n)) : list (bitvec m) := chunks_nat n m v.to_nat


  @[simp]
  lemma chunks_nat_zero {n m:ℕ}
    : chunks_nat n m 0 = list.repeat 0 n :=
    begin
      induction n with n ih,
      case nat.zero
      { simp, },
      case nat.succ
      { simp [chunks_nat_step],
        apply and.intro,
        { simp [bitvec.of_nat],
          refl,
        },
        { exact ih },
      },
    end


  @[simp]
  lemma chunks'_nil {m:ℕ} {x: bitvec (m * 0) }: chunks' _ m x = [] :=
    begin
      unfold chunks',
      unfold chunks_nat,
    end

  @[simp]
  lemma chunks'_length {n m : ℕ} {x: bitvec (m * n)} : list.length (chunks' n m x) = n :=
  begin
    induction n with n p,
    case nat.zero
    { unfold chunks', simp },
    case nat.succ
    { simp [chunks', p],
    },
  end

  @[simp]
  lemma chunks'_length_mul {n m : ℕ} {x: bitvec (m * n)}
  : m * list.length (chunks' n m x) = m * n
  := by simp

  lemma chunks'_step {n m : ℕ} (v : bitvec (m * succ n))
  : chunks' (succ n) m v = (bitvec.of_nat m (nat.shiftr v.to_nat (n*m)) :: chunks_nat n m v.to_nat) :=
  begin
    simp [chunks', chunks_nat],
  end

  def concat_nat {n : ℕ} : ℕ → list (bitvec n) → ℕ
  | acc []      := acc
  | acc (x::xs) := concat_nat (nat.shiftl acc n + x.to_nat) xs

  @[simp]
  lemma concat_nat_nil : ∀(n acc : ℕ), @concat_nat n acc list.nil = acc :=
    begin
      intros,
      simp [concat_nat]
    end

  @[simp]
  lemma concat_nat_step {n acc : ℕ} (x: bitvec n) (xs: list (bitvec n))
    : concat_nat acc (x::xs) = concat_nat (nat.shiftl acc n + x.to_nat) xs :=
    by simp [concat_nat]

  lemma concat_nat_step_acc {n r : ℕ} (ls : list (bitvec n))
  : concat_nat r ls = r * 2^(ls.length * n) + concat_nat 0 ls :=
  begin
    induction ls with l' ls' ih generalizing r,
    case list.nil
    { simp [concat_nat, mul_comm],
    },
    case list.cons
    { simp [concat_nat, bitvec.to_nat, shiftl_eq_mul_pow],
      rw [ih],
      rw [@ih l'.to_nat],
      simp,
      congr,
      simp [right_distrib, pow_distrib, mul_assoc],
    },
  end

  @[simp]
  lemma concat_nat_zeros {n m:ℕ}
  : @concat_nat n 0 (list.repeat 0 m) = 0 :=
  begin
    induction m with m ih,
    case nat.zero
    { simp, },
    case nat.succ
    { simp [bitvec.to_nat],
      exact ih,
    },
  end

  theorem concat_nat_zero_bound {n : ℕ} : ∀(l : list (bitvec n)),
    concat_nat 0 l < 2^(n*l.length) :=
  begin
    intros,
    induction l with l ls ih,
    case list.nil
    { simp, dec_trivial_tac },
    case list.cons
    { simp,
      rw [concat_nat_step_acc, mul_comm n],
      rw [mul_comm n ls.length] at ih,
      simp,
      rw [add_comm 1 ls.length],
      apply (@add_pow_bound (concat_nat 0 ls) (bitvec.to_nat l) (ls.length) n ih l.property),
    },
  end

  theorem concat_nat_bound {w:ℕ} {n:ℕ} : ∀(r:ℕ) (h:r < 2^w) (l:list (bitvec n)),
    concat_nat r l < (r + 1)*2^(l.length * n) :=
  begin
    intros,
    rw [concat_nat_step_acc],
    calc
      r * 2^(l.length * n) + concat_nat 0 l < r * 2^(l.length * n) + 2^(n * l.length)   : by apply nat.add_lt_add_left (concat_nat_zero_bound l)
                                        ... = r * 2^(l.length * n) + 2^(l.length * n)   : by rw (mul_comm n)
                                        ... = r * 2^(l.length * n) + 1*2^(l.length * n) : by simp
                                        ... = (r+1)*2^(l.length * n)                    : by rw [←right_distrib]
  end


def concat' {n : ℕ} (input: list (bitvec n)) : bitvec (n * input.length) :=
   ⟨concat_nat 0 input, concat_nat_zero_bound input⟩

  lemma chunks_nat_concat_nat_eq {n m:ℕ} (x: ℕ)
  : concat_nat 0 (chunks_nat n m x) = x % 2^(m * n) :=
  begin
    induction n with n ih,
    case nat.zero
    { simp, },
    case nat.succ
    { have: 2 > 0 := of_as_true trivial,
      rw [mod_pow_succ this],
      rw [concat_nat_step_acc],
      -- These simps cannot be combined, because it causes an error in the expander.
      simp [bitvec.to_nat, shiftr_eq_div_pow, bitvec.of_nat],
      simp [concat_nat_step_acc, ih],
      -- NOTE: not sure how to finish this, but the goal holds for the
      -- random inputs I tested it on.
      admit
    },
  end

end bitvec
