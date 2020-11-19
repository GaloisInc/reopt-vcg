import Main.Runelf
    
def main (xs : List String) : IO UInt32 :=
  match xs with 
  | [f] => do doit f; pure 0
  | _   => throwS "Expected a file"
