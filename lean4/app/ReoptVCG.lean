import ReoptVCG.Annotations


namespace ReoptVCG

inductive VerificationMode
| defaultMode : VerificationMode
| exportMode : String → VerificationMode
| runSolverMode : String → List String → VerificationMode

def isDefaultMode : VerificationMode → Bool
| VerificationMode.defaultMode => true
| _ => false


-- Like VCGArgs in Main but with all mandatory fields no longer as Options.
structure VCGConfig :=
(annFile : String)
(mode : VerificationMode)
(verbose : Bool)
          

def runVCG (cfg : VCGConfig) : IO UInt32 := do
annContents ← IO.FS.readFile cfg.annFile;
match Lean.Json.parse annContents >>= parseAnnotations with
| Except.error errMsg => do
  IO.println $ "Encountered an error while parsing the Json in `"++ cfg.annFile ++"`: "++ errMsg;
  pure 1
| Except.ok modAnn => do
  when cfg.verbose $
    IO.println $ "Parsed the JSON annotation file `"++cfg.annFile++"` successfully!";
  pure 0
  

end ReoptVCG
