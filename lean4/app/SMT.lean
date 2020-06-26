
import Galois.Data.SExp
import Galois.Init.Io
import ReoptVCG.SMTParser
import ReoptVCG.MCStdLib
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import SMTLIB.Syntax
import X86Semantics.Common

namespace ReoptVCG
open SMT
universe u

/-- Abstracts out the _specifics_ of how certain BlockExpr terms
    should be emitted as SMT terms, so that the underlying SMT
    architecture can generate these ahead of time in whatever way is
    appropriate and then simply parameterize SMT generation of
    precondition expressions accordingly. --/
class BlockExprEnv (α : Type u) :=
(initGPReg64 : α → x86.reg64 → term sort.bv64)
(fnStartRegState : α → x86.reg64 → term sort.bv64)
(evalVar : α → llvm.ident → Option (Sigma term))
(readMem : α → ∀(w : WordSize), x86.vcg.memaddr →  term w.sort)

structure BlockVCGExprEnv :=
(evalVar : llvm.ident → Option (Sigma term)) -- FIXME, this may just be state.llvmIdentMap.find? =\
(context : BlockVCGContext)
(state : BlockVCGState)

namespace BlockVCGExprEnv
variable (e : BlockVCGExprEnv)

def initGPReg64 (r : x86.reg64) : term sort.bv64 :=
e.state.mcCurRegs.get_reg64 r

def fnStartRegState (r : x86.reg64) : term sort.bv64 :=
e.context.mcStdLib.funStartRegs.get_reg64 r

def readMem (w:WordSize) (addr : x86.vcg.memaddr) : term w.sort :=
(e.context.mcStdLib.memOps w).readMem e.state.mcCurMem addr

end BlockVCGExprEnv

instance BlockVCGExprEnv.isBlockExprEnv : BlockExprEnv BlockVCGExprEnv :=
{initGPReg64 := BlockVCGExprEnv.initGPReg64,
 fnStartRegState := BlockVCGExprEnv.fnStartRegState,
 evalVar := BlockVCGExprEnv.evalVar,
 readMem := BlockVCGExprEnv.readMem
}

namespace BlockExpr

open WellFormedSExp

def ppLLVMIdent : llvm.ident → String
| llvm.ident.named nm => nm
| llvm.ident.anon n => "%"++(repr n)

def toSExp : ∀ {tp : sort}, BlockExpr tp → SExp String
| _, stackHigh => SExp.atom "stack_high"
| _, initGPReg64 r => SExp.atom r.name
| _, fnStartGPReg64 r => SExp.list [SExp.atom "fnstart", SExp.atom r.name]
| _, mcStack a w =>
  SExp.list [SExp.atom "mcstack",
             toSExp a,
             SExp.list [SExp.atom "_", SExp.atom "BitVec", SExp.atom (repr w.bits)]
            ]
| _, llvmVar nm tp => SExp.list [SExp.atom "llvm", SExp.atom (ppLLVMIdent nm)]
| _, eq e1 e2 => SExp.list [SExp.atom "=", toSExp e1, toSExp e2]
| _, bvAdd e1 e2 => SExp.list [SExp.atom "bvadd", toSExp e1, toSExp e2]
| _, bvSub e1 e2 => SExp.list [SExp.atom "bvsub", toSExp e1, toSExp e2]
| _, bvDecimal n width => SExp.list [SExp.atom "_", SExp.atom ("bv"++(repr n)), SExp.atom (repr width)]

def toString : ∀ {tp : sort}, BlockExpr tp → String
| _, e => (BlockExpr.toSExp e).toString

-- Converts an Expr into an SMT term given an environment. AMK: it's currently in IO
-- to handle some partiality (doh!) and because we want to use it in an IO context
-- at the moment any, so it's a convenient hack for the moment. TODO: maybe we
-- can guarantee all the SMT terms an llvmVar could be are inhabited and use lean4's
-- panic! and at least not force this to be in IO.
def toSMT {α : Type u} [BlockExprEnv α] (env: α) : ∀ {tp : sort}, BlockExpr tp → Except BlockVCGError (term tp)
| _, stackHigh => pure $ BlockExprEnv.fnStartRegState env x86.reg64.rsp
| _, initGPReg64 r => pure $ BlockExprEnv.initGPReg64 env r
| _, fnStartGPReg64 r => pure $ BlockExprEnv.fnStartRegState env r
| _, mcStack a w => do
  t ← toSMT a;
  pure $ BlockExprEnv.readMem env w t
| _, llvmVar nm tp =>
  match BlockExprEnv.evalVar env nm with
  | some ⟨tp', t⟩ =>
    if h : tp = tp'
    then
      let hEq : term tp' = term tp := h ▸ rfl;
      pure $ cast hEq t
    else
      Except.error $ BlockVCGError.globalErr $
      "Error while translating precondition to SMT! LLVM variable `"
      ++ nm.asString ++ "` had no entry in the phi variable map!"
  | none => Except.error $ BlockVCGError.globalErr $
    "Error while translating precondition to SMT! LLVM variable `"
    ++ nm.asString ++ "` had no entry in the phi variable map!"
| _, eq e1 e2 => do
  t1 ← toSMT e1;
  t2 ← toSMT e2;
  pure $ SMT.eq t1 t2
| _, bvAdd e1 e2 => do
  t1 ← toSMT e1;
  t2 ← toSMT e2;
  pure $ SMT.bvadd t1 t2
| _, bvSub e1 e2 => do
  t1 ← toSMT e1;
  t2 ← toSMT e2;
  pure $ SMT.bvsub t1 t2
| _, bvDecimal n width => pure $ SMT.bvimm width n

end BlockExpr

/-- Converts a BlockExpr into an SMT term in the BlockVCG context. --/
def evalPrecondition {tp : sort} (evalVar : llvm.ident → Option (Sigma term)) (expr : BlockExpr tp) : BlockVCG (term tp) := do
ctx ← read;
state ← get;
let env := BlockVCGExprEnv.mk evalVar ctx state;
match BlockExpr.toSMT env expr with
| Except.error err => throw err
| Except.ok res => pure res


def ppBlockLabel (lbl:llvm.block_label) : String :=
match lbl.label with
| llvm.ident.named str => str
| llvm.ident.anon n => "anon" ++ n.repr

-- | Pretty print an error that occurs at the start of an instruction.
def renderMCInstError (fnm : String) (blockLbl : llvm.block_label) (idx : Nat) (addr : Nat) (msg : String) : String :=
fnm++"."++(ppBlockLabel blockLbl)++"."++idx.repr++"("++addr.ppHex++"). "++msg

def standaloneGoalFilename (fnName : String) (lbl : llvm.block_label) (goalIndex : Nat) : String :=
fnName ++ "_" ++ (ppBlockLabel lbl) ++ "_" ++ goalIndex.repr ++ ".smt2"

/-- Return the absolute path to the directory where we can stash
    temporary files during IO computations. --/
def getTemporaryDirectory : IO String := do
if !System.Platform.isWindows
then pure "/tmp"
else do
  let validateDir : String → String → IO String := (λ envVar dir => do
    isValid ← IO.isDir dir;
    if isValid
    then pure dir
    else throw $ IO.userError $ "Temporary directory specified by `"++envVar
                                ++"` environment variable (i.e., `"++dir++"`) does not exist.");
  tempMaybeStr ← IO.getEnv "TEMP";
  tmpMaybeStr ← IO.getEnv "TMP";
  match tempMaybeStr, tmpMaybeStr with
  | some tmpDir, _ => validateDir "TEMP" tmpDir
  | _, some tmpDir => validateDir "TMP" tmpDir
  | _, _ => throw $ IO.userError $ "FATAL ERROR! On Windows, a temporary directory "
                                   ++ "must be specified in the environment variable `TEMP` (or `TMP`)."

/-- Like `standaloneGoalFilename`, but gives an absolute path to a filename in the OS's temporary directory.--/
def temporaryStandaloneGoalFilepath (fnName : String) (lbl : llvm.block_label) (goalIndex : Nat) : IO String := do
tempDir ← getTemporaryDirectory;
pure $ System.mkFilePath [tempDir, standaloneGoalFilename fnName lbl goalIndex]


/-- Common things appearing at the top of every  --/
def checkNegatedGoalInContext (goalName : String) (negatedGoal : term sort.smt_bool) (ctx : smtM Unit) : smtM Unit := do
comment goalName;
setLogic Raw.logic.all;
setProduceModels true;
ctx;
checkSatAssuming [negatedGoal];
exit


/-- Write assert the negated goal and write out the resulting script
    of commands to a file. -/
def exportCheckSatProblem
(outputDir fnName : String)
(blockLabel : llvm.block_label)
(goalCounter : IO.Ref Nat)
(cmdRef : IO.Ref (smtM Unit))
(negatedGoal : term sort.smt_bool)
(goalName : String)
: IO Unit := do
cnt ← goalCounter.get;
smtCtx ← cmdRef.get;
goalCounter.modify Nat.succ;
let (_, _, cmds) := runsmtM IdGen.empty (checkNegatedGoalInContext goalName negatedGoal smtCtx);
let filePath := System.mkFilePath [outputDir, standaloneGoalFilename fnName blockLabel cnt];
file ← IO.FS.Handle.mk filePath IO.FS.Mode.write;
cmds.forM $ λ c => file.putStr $ (toString (toSExpr c)) ++ "\n"


def defaultAddSMTCallback (cmdRef : IO.Ref (smtM Unit)) : SMT.smtM Unit → IO Unit :=
λ action => cmdRef.modify (λ cmds => cmds *> action)

def defaultAddCommandCallback (cmdRef : IO.Ref (smtM Unit)) : command → IO Unit :=
λ cmd => cmdRef.modify (λ cmds => cmds *> liftCommand cmd)

def exportCallbacks
{α}
(outputDir fnName : String)
(blockLabel : llvm.block_label)
(action : ProverInterface → IO α)
: IO α
:= do
goalCounter <- IO.mkRef 0;
let initSmtM : smtM Unit := pure ();
cmdRef <- IO.mkRef initSmtM;
action
  {addSMTCallback := defaultAddSMTCallback cmdRef,
   addCommandCallback := defaultAddCommandCallback cmdRef,
   proveFalseCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef p msg,
   proveTrueCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef (SMT.not p) msg,
   blockErrorCallback := λ i a msg =>
    -- FIXME stderr and other handles are in Lean4, fix when we bump next
    IO.println $ "Error: " ++ renderMCInstError fnName blockLabel i a msg
  }


------------------------------------------------------------------------
-- Interactive session

-- | Information needed for interatively verifying goal.
structure InteractiveContext :=
(annFile : String)
-- ^ Annotation file (for error-reporting purposes)
(fnName : FnName)
-- ^ Name of function to verify
(blockLabel : llvm.block_label)
-- ^ Label of block
(allGoalCounter : IO.Ref Nat)
-- ^ Counter for all goals (i.e., the total number)
(verifiedGoalCounter : IO.Ref Nat)
-- ^ Counter for all successfully verified goals.
(blockGoalCounter : IO.Ref Nat)
-- ^ Index of goal to discharge within block
(solverCommand : String)
-- ^ Command line contents, which when followed up a file name, can be executed
--   to see if the resulting script is satisfiable or not.


-- | Function to verify an SMT proposition is provable in the given
-- | context and print the result to the user.
def interactiveVerifyGoal
(ictx : InteractiveContext)
-- ^ Context for verifying goals
(cmdRef : IO.Ref (smtM Unit))
-- ^ The SMT context the goal should be proven in
(negGoal : SMT.term SMT.sort.smt_bool)
-- ^ Negation of goal to verify
(propName : String)
-- ^ Name of proposition for reporting purposes.
: IO Unit := do
cnt ← ictx.blockGoalCounter.get;
ictx.allGoalCounter.modify Nat.succ;
ictx.blockGoalCounter.modify Nat.succ;
let fname := standaloneGoalFilename ictx.fnName ictx.blockLabel cnt;
smtFilePath ← temporaryStandaloneGoalFilepath ictx.fnName ictx.blockLabel cnt;
let resultFilePath := smtFilePath ++ ".result";
-- FIXME was stderr, fix with next Lean4 bump
IO.print $ "  Verifying " ++ propName ++ "... ";
-- FIXME, uncomment this line after next lean4 bump
-- IO.stdout.flush;
smtCtx ← cmdRef.get;
let (_, _, cmds) := runsmtM IdGen.empty (checkNegatedGoalInContext propName negGoal smtCtx);
IO.FS.withFile smtFilePath IO.FS.Mode.write (λ file => do
  cmds.forM (λ c => do file.putStr (toString (toSExpr c)); unless c.isComment $ file.putStr "\n");
  file.flush);
Galois.IO.system $ ictx.solverCommand++" "++smtFilePath++" > " ++resultFilePath;
smtResult ← IO.FS.lines resultFilePath;
-- FIXME, this assumes the file has a single word in it essentially... might want to
-- make it slightly more complicated if
let printExportInstructions : IO Unit := (do
  -- FIXME print to stderr after next lean4 bump
  IO.println $ "    To see the output, run `reopt-vcg "++ictx.annFile++" --export <dir>`";
  IO.println $ "    The SMT query will be stored in <dir>"
               ++[System.FilePath.pathSeparator].asString++(standaloneGoalFilename ictx.fnName ictx.blockLabel cnt));
match smtResult.get? 0 with
| none => do
  -- FIXME print to stderr on next lean4 bump (these and all below printlns in this function)
  IO.println "ERROR";
  IO.println "";
  IO.println "    Verification failed: no response from the SMT solver was detected.";
  printExportInstructions
| some checkSatRes =>
  match parseCheckSatResult checkSatRes with
  | CheckSatResult.unsat => do
    ictx.verifiedGoalCounter.modify Nat.succ;
    IO.println $ "OK"
  | CheckSatResult.sat => do
    IO.println $ "FAIL";
    IO.println $ "    Verification failed: the SMT query returned `sat`";
    IO.println $ "";
    printExportInstructions
  | CheckSatResult.unknown => do
    IO.println $ "FAIL";
    IO.println $ "    Verification failed: the SMT query returned `unknown`";
    IO.println $ "";
    printExportInstructions
  | CheckSatResult.unsupported => do
    IO.println $ "ERROR";
    IO.println $ "    Verification failed: the SMT query returned `unsupported`";
    IO.println $ "";
    printExportInstructions
  | CheckSatResult.unrecognized msg => do
    IO.println $ "ERROR";
    IO.println $ "    Verification failed: the SMT solver did not return a recognized response to `check-sat-assuming`.";
    IO.println $ "";
    IO.println $ "    Response: ";
    smtResult.forM IO.println;
    IO.println $ "";
    IO.println $ "";
    IO.println $ "    This failure likely reflects a bug in reopt-vcg.";
    IO.println $ "";
    printExportInstructions




def newInteractiveSession
(annFile solverPath : String)
(solverArgs : List String)
(allGoalCounter verifiedGoalCounter errorCounter : IO.Ref Nat)
(fnName : FnName)
(lbl : llvm.block_label)
(action : ProverInterface → IO Unit)
: IO Unit := do
-- Create Goal counter for just this block.
blockGoalCounter ← IO.mkRef 0;
let solverCmd := String.intercalate " " (solverPath::solverArgs);
let initSmtM : smtM Unit := pure ();
cmdRef <- IO.mkRef initSmtM;
let ictx : InteractiveContext:=
  { annFile := annFile,
    fnName := fnName,
    blockLabel := lbl,
    allGoalCounter := allGoalCounter,
    verifiedGoalCounter := verifiedGoalCounter,
    blockGoalCounter := blockGoalCounter,
    solverCommand := solverCmd
  };
let fns : ProverInterface :=
  {addSMTCallback := defaultAddSMTCallback cmdRef,
   addCommandCallback := defaultAddCommandCallback cmdRef,
   proveFalseCallback := λ p => interactiveVerifyGoal ictx cmdRef p,
   proveTrueCallback := λ p => interactiveVerifyGoal ictx cmdRef (SMT.not p),
   blockErrorCallback := λ i a msg => do
     -- FIXME stderr and other handles are in Lean4, fix when we bump next
     IO.println $ "Error: " ++ (renderMCInstError fnName lbl i a msg);
     errorCounter.modify Nat.succ
  };
action fns


def interactiveSMTGenerator (annFile solverPath : String) (solverArgs : List String) : IO ProverSessionGenerator := do
-- Counter for all goals
allGoalCounter ← IO.mkRef 0;
-- Counter for goals successfully verified.
verifiedGoalCounter <- IO.mkRef 0;
-- Counter for errors
errorCounter <- IO.mkRef 0;
let whenDone : IO UInt32 := (do
  allCnt ← allGoalCounter.get;
  verCnt ← verifiedGoalCounter.get;
  errorCnt ← errorCounter.get;
  let verSuccess := errorCnt == 0 && verCnt == allCnt;
  if verSuccess then
    IO.println "Verification of all goals succeeded."
   else
    IO.println "Verification of all goals failed.";
  IO.println $ "Verified "++(repr verCnt)++"/"++(repr allCnt)++" goal(s).";
  when (errorCnt > 0) $
    IO.println $ "Encountered"++(repr errorCnt)++"error(s).";
  pure $ if verSuccess then 0 else 1);
pure { blockCallback :=
        newInteractiveSession annFile solverPath solverArgs
          allGoalCounter verifiedGoalCounter errorCounter,
       sessionComplete := whenDone
     }

end ReoptVCG
