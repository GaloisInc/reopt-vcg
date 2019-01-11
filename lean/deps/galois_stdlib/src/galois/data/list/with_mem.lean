namespace list

def map_with_mem {α} {β: Sort _} : Π(l:list α), (Π(x:α), x ∈ l → β) → list β
| [] f := []
| (h::r) f
  := f h (or.inl rfl)
  :: map_with_mem r (λ(x:α) (p:x ∈ r), f x (or.inr p))

/- Elements in a list have a smaller size than the list. -/
theorem mem_sizeof {α} [s : has_sizeof α] {x : α} {l : list α} (p : x ∈ l)
: sizeof x < l.sizeof :=
begin
  induction l,
  case nil {
    exact false.elim p,
  },
  case cons : h r ind {
    simp [has_mem.mem, list.mem] at p,
    simp [list.sizeof, nat.succ_add],
    apply nat.succ_le_succ,
    cases p,
    case or.inl : x_eq_h {
      simp [x_eq_h],
      apply nat.le_add_left,
    },
    case or.inr : x_in_r {
      transitivity, exact le_of_lt (ind x_in_r),
      apply nat.le_add_right,
    },
  },
end

--- A decidable test for lists using a test for elements that
-- includes proof only list elements are queried.
def has_dec_eq_with_mem {α}
: Π (k l : list α) (p : Π{a : α}, a ∈ k → Π{b:α}, b ∈ l → decidable (a = b)),
    decidable (k = l)
| []      [] p    := is_true rfl
| (a::as) [] p    := is_false (λ h, list.no_confusion h)
| []      (b::bs) p := is_false (λ h, list.no_confusion h)
| (a::as) (b::bs) p :=
  let ma : a ∈ (a::as) := or.inl rfl in
  let mb : b ∈ (b::bs) := or.inl rfl in
  match p ma mb with  | is_true hab :=
    let q (x:α) (xm:x ∈ as) (y:α) (ym:y ∈ bs) :=
          p (or.inr xm) (or.inr ym) in
    match has_dec_eq_with_mem as bs q with
    | is_true habs  :=
      is_true (eq.subst hab (eq.subst habs rfl))
    | is_false nabs :=
      is_false (λ h, list.no_confusion h (λ _ habs, absurd habs nabs))
    end
  | is_false nab := is_false (λ h, list.no_confusion h (λ hab _, absurd hab nab))
  end

/-
Predicate that returns true if two lists have same length and all
 pairswise elements are equivalent.
-/
inductive holds_pairwise {α} {β} (P : α → β → Prop)
: list α -> list β -> Prop
| nil {} : holds_pairwise [] []
| cons {} {x:α} {xr : list α} {y:β} {yr:list β}
  : P x y
  → holds_pairwise xr yr
  → holds_pairwise (x::xr) (y::yr)

namespace holds_pairwise
open decidable

/- Decide the holds pairwise relation. -/
def decide_with_mem {α} {β} (r : α → β → Prop)
: Π(x:list α) (y:list β),
   (Π(a:α), a ∈ x → Pi(b:β), b ∈ y → decidable (r a b))
    → decidable (holds_pairwise r x y)
| [] [] _ := is_true nil
| [] (yh::yr) _ := is_false (by { intro p, cases p, })
| (xh::xr) [] _ := is_false (by { intro p, cases p, })
| (xh::xr) (yh::yr) p :=
  match p xh (or.inl rfl) yh (or.inl rfl) with
  | is_true ph :=
    let q := λa am b bm, p a (or.inr am) b (or.inr bm) in
    match decide_with_mem xr yr q with
    | is_true pr := is_true (cons ph pr)
    | is_false npr := is_false
      begin
        intro p,
        cases p with x yr y yr ph pr,
        exact npr pr,
      end
    end
  | is_false nph := is_false
    begin
      intro p,
      cases p with x yr y yr ph pr,
      exact nph ph,
    end
  end

end holds_pairwise

end list
