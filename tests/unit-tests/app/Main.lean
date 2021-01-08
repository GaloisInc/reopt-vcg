
import Std.Data.RBMap
import Test.AnnotationParsing
import Test.Hex
import Test.JsonRoundtrip
import Test.LoadElf
import Test.SExp


namespace Test

def tests : Std.RBMap String (IO UInt32) (λ x y => x < y) :=
  Std.RBMap.fromList 
  [("AnnotationParsing.lean", AnnotationParsing.test),
   ("Hex.lean", Hex.test),
   ("JsonRoundtrip.lean", JsonRoundtrip.test),
   ("LoadElf.lean", LoadElf.test),
   ("SExp.lean", SExp.test)
  ]
  (λ x y => x < y)

end Test


def main(args : List String) : IO UInt32 := do
  match args with
  | [testFile] => 
    match Test.tests.find? testFile with
    | Option.none =>
      throw $ IO.userError $ "Test corresponding to file not found: "
                             ++ testFile ++ " (see tests/unit-tests/app/Main.lean)"
    | Option.some test => test
  | _ =>
      throw $ IO.userError $ "Error: expected a single test file name as an argument, but got " ++ args.toString
