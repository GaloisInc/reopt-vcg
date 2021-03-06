
import ReoptVCG.Annotations
import ReoptVCG.ReoptVCG

open ReoptVCG

-- Modes of execution for `reopt-vcg`
inductive VCGCmd
| showHelp : VCGCmd
| runVCG : VCGConfig → VCGCmd


-- A container to accumulate user-provided command line arguments in
-- while the are being processed.
structure VCGArgs := 
  (annFile : Option String)
  (mode : Option VerificationMode)
  (verbose : Bool)
  (semanticsBackend : SemanticsBackend)

-- | State of argument parsing before any user arguments have actually
-- been processed.

def initVCGArgs := VCGArgs.mk none none false SemanticsBackend.KSemantics

-- Function for parsing command line arguments to reopt-vcg.
partial def parseArgs : List String → VCGArgs → Except String VCGCmd
| [], args => do 
  let annPath <- (args.annFile.map Except.ok).getD (throw "Missing VCG file to run.")
  let mut mode := match args.mode with
                  | none => VerificationMode.default
                  | some m => m
  pure $ VCGCmd.runVCG $ VCGConfig.mk annPath mode args.verbose args.semanticsBackend
| (s::ss), args =>
  if s == "--help" then
    pure $ VCGCmd.showHelp
  else if s == "--verbose" || s == "-v" then
    parseArgs ss $ {args with verbose := true}
  else if s == "--export" then do
    unless args.mode.isNone do throw "Cannot specify --export or --solver multiple times."
    match ss with
    | [] => throw "missing argument for `--export` flag"
    | s'::ss' =>
    parseArgs ss' $ {args with mode := some $ VerificationMode.exportMode s'}
  else if s == "--solver" then do
    unless args.mode.isNone do throw "Cannot specify --export or --solver multiple times.";
    match ss with
    | [] => throw "missing argument for `--solver` flag"
    | s'::ss' =>
    match String.split s' Char.isWhitespace with
    | [] => throw "Expected a solver name and command line argument(s)."
    | (solver::solverArgs) =>
      let vm := VerificationMode.solverMode {SolverConfig.default with solverPathAndArgs := some (solver, solverArgs)}
      parseArgs ss' $ {args with mode := some vm}
    else if s == "--alt-backend" then
    parseArgs ss $ {args with semanticsBackend := SemanticsBackend.ManualSemantics}
  else if s == "--json-goals" then do
    match ss with
    | [] => throw "missing argument for `--json-goals` flag"
    | s'::ss' =>
      let mut mode := args.mode
      match args.mode with
      | none =>
        mode := some (VerificationMode.solverMode {SolverConfig.default with jsonOut := some s'})
      | some (VerificationMode.exportMode _) =>
        throw "Cannot specify `--json-goals` with `--export`."
      | some (VerificationMode.solverMode solverCfg) =>
        if solverCfg.jsonOut.isSome then do
          throw "Cannot specify `--json-goals` multiple times."
        mode := some $ VerificationMode.solverMode {solverCfg with jsonOut := some s'}
      parseArgs ss' $ {args with mode := mode}
  else do 
    if (String.isPrefixOf "--" s) then throw $ "Unexpected flag " ++ s
    if (Option.isSome args.annFile) then throw "Multiple VCG files specified."
    parseArgs ss $ {args with annFile := (Option.some s)}


def showUsage : IO Unit := do
  IO.println "Usage: reopt-vcg [-v|--verbose] <input.json> [--alt-backend] {--export <export-dir> | --solver <solver-path>} [--json-goals <json-path>]"
  
def showHelp : IO Unit := do
  showUsage;
  IO.println
    $  "reopt-vcg generates verification conditions to prove that reopt generated\n"
    ++ "   LLVM is faithful to the input binary.\n"


def main (args:List String) : IO UInt32 :=
  match parseArgs args initVCGArgs with
  | Except.error msg => do
    IO.println $ "Error encountered while parsing reopt-vcg command line arguments: " ++ msg;
    showUsage;
    pure 1
  | Except.ok VCGCmd.showHelp => do showHelp; pure 0
  | Except.ok (VCGCmd.runVCG cfg) => runVCG cfg
      
