
import Init.Data.RBMap
import Test.AnnotationParsing
import Test.Hex
import Test.JsonRoundtrip
import Test.LoadElf
import Test.SExp
import Test.SMTExport


namespace Test

def tests : RBMap String (IO UInt32) (λ x y => x < y) :=
  RBMap.fromList 
  [("AnnotationParsing.lean", AnnotationParsing.test),
   ("Hex.lean", Hex.test),
   ("JsonRoundtrip.lean", JsonRoundtrip.test),
   ("LoadElf.lean", LoadElf.test),
   ("SExp.lean", SExp.test),
   ("SMTExport.lean", SMTExport.test)
  ]
  (λ x y => x < y)

end Test

def main(args : List String) : IO UInt32 := do
match args with
| [testFile] => 
  match Test.tests.find? testFile with
  | Option.none =>
    throw $ IO.userError $ "Test corresponding to file not found: " ++ testFile ++ " (see tests/Main.lean)"
  | Option.some test => test
| _ =>
    throw $ IO.userError $ "Error: expected a single test file name as an argument, but got " ++ args.toString
