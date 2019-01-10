-- Boolean operations.

/- Implication over Booleans. -/
def bimplies : bool → bool → bool
| tt y := y
| ff _ := tt

/- Return conjunction of all elements in list. -/
def ball : list bool → bool
| [] := tt
| (tt::r) := ball r
| (ff::r) := ff

/- Return disjunction of all elements in list. -/
def bany : list bool → bool
| [] := ff
| (tt::r) := tt
| (ff::r) := bany r
