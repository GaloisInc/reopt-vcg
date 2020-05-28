
import Init.Data.RBMap
import Test.JsonRoundtrip

namespace Test

def tests : RBMap String (IO UInt32) (λ x y => x < y) :=
  RBMap.fromList 
  [ ("JsonRoundtrip.lean", JsonRoundtrip.test)]
  (λ x y => x < y)

end Test

def main(args : List String) : IO UInt32 := do
match args with
| [testFile] => 
  match Test.tests.find? testFile with
  | Option.none => throw $ IO.userError $ "Test file not found: " ++ testFile
  | Option.some test => test
| _ => throw $ IO.userError $ "Error: expected a single test file name as an argument, but got " ++ args.toString
