
namespace option

section

parameter {α : Type _}

/- Is some as a Prop instead of Boolean -/
inductive is_some_prop : option α → Prop
| intro (x:α) : is_some_prop (option.some x)

open decidable

instance is_some_prop.decidable : Π(x:option α), decidable (is_some_prop x)
| none := is_false (by { intro p, cases p, })
| (some x) := is_true (is_some_prop.intro x)


end

@[simp]
theorem is_some_prop_none {α : Type _} :
  (@option.is_some_prop α none) ↔ false :=
begin
  apply iff.intro,
  { intro x, cases x, },
  { intro x, exact (false.elim x), },
end

@[simp]
theorem is_some_prop_map {α β : Type _} (x:option α) (f:α → β) :
  option.is_some_prop (option.map f x) ↔ option.is_some_prop x :=
begin
  cases x; simp [option.map, option.bind],
  case option.some : x {
    apply iff.intro; intro p; apply (is_some_prop.intro _),
  },
end

/- Get the value assuming we have a proof. -/
def is_some_prop.get {α} : Π{x:option α}, is_some_prop x → α
| none p :=
  begin
    apply false.elim,
    cases p,
  end
| (some x) p := x

@[simp]
theorem is_some_prop.some_get {α : Type} {x:option α} (p:option.is_some_prop x)
 : some p.get = x :=
begin
  cases p with x,
  simp [is_some_prop.get],
end

theorem get_is_some_prop_map {α β : Type _} (x:option α) (f : α → β)
  (p : option.is_some_prop (option.map f x))
: f (option.is_some_prop.get ((option.is_some_prop_map x f).mp p))
  = option.is_some_prop.get p :=
begin
  apply option.some.inj,
  simp [is_some_prop.some_get],
  cases x,
  case option.none : {
    simp at p,
    exact false.elim p,
  },
  case option.some : {
    simp [is_some_prop.get],
  },
end


end option
