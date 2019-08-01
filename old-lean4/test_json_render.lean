import json
open json

def mkTree : ℕ → Value
| 0 := Value.null
| (Nat.succ n) :=
  let t := mkTree n in
  Value.listObj [("a", t), ("b", t)]

open IO.Fs

def main (xs : List String) : IO Unit := do
  let t := mkTree xs.head.toNat,
  let val := toString t,
  IO.println ((toString t).length)
