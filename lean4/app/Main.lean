
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
(mode : VerificationMode)
(verbose : Bool)

-- | State of argument parsing before any user arguments have actually
-- been processed.
def initVCGArgs := VCGArgs.mk Option.none VerificationMode.defaultMode true

-- Function for parsing command line arguments to reopt-vcg.
partial def parseArgs : List String →  VCGArgs → Except String VCGCmd
| [], args => do 
  annPath <- (args.annFile.map Except.ok).getD (throw "Missing VCG file to run.");
  pure $ VCGCmd.runVCG $ VCGConfig.mk annPath args.mode args.verbose
| (s::ss), args =>
  if s == "--help" then
    pure $ VCGCmd.showHelp
  else if s == "--verbose" then
    parseArgs ss $ {args with verbose := true}
  else if s == "--export" then do 
    unless args.mode.isDefault $ throw "Cannot specify --export or --solver multiple times.";
    match ss with
    | [] => throw "missing argument for `--export` flag"
    | s'::ss' =>
    parseArgs ss' $ {args with mode := VerificationMode.exportMode s'}
  else if s == "--solver" then do
    unless args.mode.isDefault $ throw "Cannot specify --export or --solver multiple times.";
    match ss with
    | [] => throw "missing argument for `--solver` flag"
    | s'::ss' =>
    match String.split s' Char.isWhitespace with
    | [] => throw "Expected a solver name and command line argument(s)."
    | (solver::solverArgs) =>
      parseArgs ss' $ {args with mode := VerificationMode.runSolverMode solver solverArgs}
  else do 
    when (String.isPrefixOf "--" s) $ throw $ "Unexpected flag " ++ s;
    when (Option.isSome args.annFile) $ throw "Multiple VCG files specified.";
    parseArgs ss $ {args with annFile := (Option.some s)}


def showUsage : IO Unit := do
IO.println "Usage: reopt-vcg [--verbose] <input.json> {--export <export-dir> | --solver <solver-path>}"
  
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
      
