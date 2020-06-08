
import ReoptVCG.Annotations
import Init.Lean.Data.Json
import Init.Lean.Data.Json.FromToJson
import Galois.Init.Json

namespace Test

namespace JsonRoundtrip

-- Parses the contents of the specified file first as a Json object
-- then as a ModuleAnnotation, which is then re-converted into a Json
-- string and reparsed as Json again. The initial and final Json
-- objects are checked for equivalence, returning "pass" if they
-- are equivalent or some error string if they are not.
def roundtripTest (annFile : String) : IO String := do
fileContents ← IO.FS.readFile annFile;
match Lean.Json.parse fileContents with
| Except.error errMsg => pure $ "Failed to parse json in `"++annFile++"`: " ++ errMsg
| Except.ok js =>
  match ReoptVCG.parseAnnotations js with
  | Except.error errMsg => pure $ "Failed to parse json as a module annotation: " ++ errMsg
  | Except.ok modAnn =>
    let str := toString $ modAnn.toJson;
    match Lean.Json.parse str with
    | Except.error errMsg => pure $ "Failed to re-parse json from `"++annFile++"`: "++errMsg
    | Except.ok js' =>
      if Lean.Json.isEqv js js'
      then pure "pass"
      else pure $ "The following are not equivalent Json values: \n"++str++"\n\nand\n\n"++(toString js')


def test : IO UInt32 := do
roundtripTest "../test-programs/test_fib_diet_reopt.ann" >>= IO.println;
roundtripTest "../test-programs/test_add_diet_reopt.ann" >>= IO.println;
pure 0

end JsonRoundtrip
end Test


