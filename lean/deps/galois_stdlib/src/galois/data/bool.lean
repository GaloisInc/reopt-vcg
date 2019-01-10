/- Boolean operations. -/

def bimplies : bool → bool → bool
| tt y := y
| ff _ := tt

def band_all : list bool → bool
| [] := tt
| (tt::r) := band_all r
| (ff::r) := ff
