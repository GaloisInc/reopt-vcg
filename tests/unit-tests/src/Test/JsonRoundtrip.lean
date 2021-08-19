
import ReoptVCG.Annotations
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Galois.Init.Json

namespace Test

namespace JsonRoundtrip

-- Parses the contents of the specified file first as a Json object
-- then as a ModuleAnnotation, which is then re-converted into a Json
-- string and reparsed as Json again. The initial and final Json
-- objects are checked for equivalence, returning "pass" if they
-- are equivalent or some error string if they are not.
def roundtripTest (annFile : String) : IO String := do
  let fileContents ← IO.FS.readFile annFile;
  match Lean.Json.parse fileContents with
  | Except.error errMsg => pure $ "Failed to parse json in `"++annFile++"`: " ++ errMsg
  | Except.ok js =>
    match ReoptVCG.ModuleAnnotations.fromJson js with
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
  let homeDir ← (do
    let maybeVal ← IO.getEnv "REOPTVCGHOME";
    pure $ maybeVal.getD (panic "REOPTVCGHOME environment variable not set"));
  roundtripTest (homeDir ++ "/test-programs/test_fib_diet_reopt.ann") >>= IO.println;
  roundtripTest (homeDir ++ "/test-programs/test_add_diet_reopt.ann") >>= IO.println;
  pure 0

end JsonRoundtrip
end Test

