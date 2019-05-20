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
  (match readFromString val Value.readValue with
  | (EState.Result.ok r _) :=
    IO.println "Success"
  | (EState.Result.error e _) := do
     IO.println "Error",
     IO.println e)
