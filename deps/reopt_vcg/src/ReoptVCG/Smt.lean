
import Galois.Data.SExp
import Galois.Init.Io
import ReoptVCG.SmtParser
import ReoptVCG.MCStdLib
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import SmtLib.Smt
import X86Semantics.Common

namespace ReoptVCG
open Smt
universe u

abbrev GoalName := String

-- structure ProverInterface :=
-- (checkSatAssuming  : GoalName → SmtM (Term SmtSort.bool) → IO Unit)
-- (blockErrorCallback : Nat → Nat → String → IO Unit) -- what do we do there? Do nothing for now...?

structure ProverSession :=
(verifyGoal : VerificationGoal → IO Unit)
(sessionComplete : IO UInt32)


def defaultCVC4Args : List String :=
-- N.B., as of CVC4 46591b1c92fc9ecd4a0997242030a1a48166301b the `--arrays-exp` flag
-- enables `--fmf-bound` by default to help with some `sat` queries; it shouldn't affect
-- `unsat` queries allegedly but appears to currently (i.e., some which should produce
-- `unsat` instead produce `unknown`) so we manually pass the `--no-fmf-bound` flag to
-- avoid the `unknown`s.
["--lang=smt2", "--arrays-exp", "--no-fmf-bound", "--incremental"]

/- Abstracts out the _specifics_ of how certain BlockExpr terms
    should be emitted as SMT terms, so that the underlying SMT
    architecture can generate these ahead of time in whatever way is
    appropriate and then simply parameterize SMT generation of
    precondition expressions accordingly. -/
class BlockExprEnv (α : Type u) :=
(initGPReg64 : α → x86.reg64 → Term SmtSort.bv64)
(initFlag : α → x86.flag → Term SmtSort.bool)
(fnStartRegState : α → x86.reg64 → Term SmtSort.bv64)
(evalVar : α → LLVM.Ident → Option (Sigma Term))
(readMem : α → ∀(w : WordSize), x86.vcg.memaddr →  Term w.sort)

structure BlockVCGExprEnv :=
(evalVar : LLVM.Ident → Option (Sigma Term)) -- FIXME, this may just be state.llvmIdentMap.find? =\
(context : BlockVCGContext)
(state : BlockVCGState)

namespace BlockVCGExprEnv
variable (e : BlockVCGExprEnv)

def initGPReg64 (r : x86.reg64) : Term SmtSort.bv64 :=
e.state.mcCurRegs.get_reg64 r

def initFlag (r : x86.flag) : Term SmtSort.bool :=
e.state.mcCurRegs.get_flag' r

def fnStartRegState (r : x86.reg64) : Term SmtSort.bv64 :=
e.context.mcStdLib.funStartRegs.get_reg64 r

def readMem (w:WordSize) (addr : x86.vcg.memaddr) : Term w.sort :=
(e.context.mcStdLib.memOps w).readMem e.state.mcCurMem addr

end BlockVCGExprEnv

instance BlockVCGExprEnv.isBlockExprEnv : BlockExprEnv BlockVCGExprEnv :=
{initGPReg64 := BlockVCGExprEnv.initGPReg64,
 initFlag    := BlockVCGExprEnv.initFlag,
 fnStartRegState := BlockVCGExprEnv.fnStartRegState,
 evalVar := BlockVCGExprEnv.evalVar,
 readMem := BlockVCGExprEnv.readMem
}

namespace BlockExpr

open WellFormedSExp

def ppLLVMIdent : LLVM.Ident → String
| LLVM.Ident.named nm => nm
| LLVM.Ident.anon n => "%"++(repr n)

def toSExp : ∀ {tp : SmtSort}, BlockExpr tp → SExp String
| _, stackHigh => SExp.atom "stack_high"
| _, initGPReg64 r => SExp.atom r.name
| _, initFlag r    => SExp.atom r.name
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

def toString : ∀ {tp : SmtSort}, BlockExpr tp → String
| _, e => (BlockExpr.toSExp e).toString

-- Converts an Expr into an SMT term given an environment. AMK: it's currently in IO
-- to handle some partiality (doh!) and because we want to use it in an IO context
-- at the moment any, so it's a convenient hack for the moment. TODO: maybe we
-- can guarantee all the SMT terms an llvmVar could be are inhabited and use lean4's
-- panic! and at least not force this to be in IO.
def toSmt {α : Type u} [BlockExprEnv α] (env: α) : ∀ {tp : SmtSort}, BlockExpr tp → Except BlockVCGError (Term tp)
| _, stackHigh => pure $ BlockExprEnv.fnStartRegState env x86.reg64.rsp
| _, initGPReg64 r => pure $ BlockExprEnv.initGPReg64 env r
| _, initFlag r    => pure $ BlockExprEnv.initFlag env r
| _, fnStartGPReg64 r => pure $ BlockExprEnv.fnStartRegState env r
| _, mcStack a w => do
  let t ← toSmt env a
  pure $ BlockExprEnv.readMem env w t
| _, llvmVar nm tp =>
  match BlockExprEnv.evalVar env nm with
  | some ⟨tp', t⟩ =>
    if h : tp = tp'
    then
      let hEq : Term tp' = Term tp := h ▸ rfl
      pure $ cast hEq t
    else
      Except.error $ BlockVCGError.globalErr $
      "Error while translating precondition to SMT! LLVM variable `"
      ++ nm.asString ++ "` had no entry in the phi variable map!"
  | none => Except.error $ BlockVCGError.globalErr $
    "Error while translating precondition to SMT! LLVM variable `"
    ++ nm.asString ++ "` had no entry in the phi variable map!"
| _, eq e1 e2 => do
  let t1 ← toSmt env e1
  let t2 ← toSmt env e2
  pure $ Smt.eq t1 t2
| _, bvAdd e1 e2 => do
  let t1 ← toSmt env e1
  let t2 ← toSmt env e2
  pure $ Smt.bvadd t1 t2
| _, bvSub e1 e2 => do
  let t1 ← toSmt env e1
  let t2 ← toSmt env e2
  pure $ Smt.bvsub t1 t2
| _, bvDecimal n width => pure $ Smt.bvimm width n

end BlockExpr

/- Converts a BlockExpr into an SMT term in the BlockVCG context. -/
def evalPrecondition {tp : SmtSort} (evalVar : LLVM.Ident → Option (Sigma Term)) (expr : BlockExpr tp) : BlockVCG (Term tp) := do
  let ctx ← read
  let state ← get
  let env := BlockVCGExprEnv.mk evalVar ctx state
  match BlockExpr.toSmt env expr with
  | Except.error err => throw err
  | Except.ok res => pure res


def ppBlockLabel (lbl:LLVM.BlockLabel) : String :=
match lbl.label with
| LLVM.Ident.named str => str
| LLVM.Ident.anon n => "anon" ++ n.repr

-- | Pretty print an error that occurs at the start of an instruction.
def renderMCInstError (fnm : String) (blockLbl : LLVM.BlockLabel) (llvmInstrIdx : Nat) (addr : Nat) (msg : String) : String :=
  fnm++"."++(ppBlockLabel blockLbl)++"."++llvmInstrIdx.repr++" @ "++addr.ppHex++": "++msg

def standaloneGoalFilename (vg : VerificationGoal) : String :=
  vg.fnName ++ "_" ++ (ppBlockLabel vg.blockLbl) ++ "_" ++ vg.goalIndex.repr ++ ".smt2"

/- Return the absolute path to the directory where we can stash
    temporary files during IO computations. -/
def getTemporaryDirectory : IO String := do
  if !System.Platform.isWindows
  then pure "/tmp"
  else do
    let validateDir : String → String → IO String := (λ envVar dir => do
      let isValid ← IO.isDir dir
      if isValid
      then pure dir
      else throw $ IO.userError $ "Temporary directory specified by `"++envVar
                                ++"` environment variable (i.e., `"++dir++"`) does not exist.")
    let tempMaybeStr ← IO.getEnv "TEMP"
    let tmpMaybeStr ← IO.getEnv "TMP"
    match tempMaybeStr, tmpMaybeStr with
    | some tmpDir, _ => validateDir "TEMP" tmpDir
    | _, some tmpDir => validateDir "TMP" tmpDir
    | _, _ => throw $ IO.userError $ "FATAL ERROR! On Windows, a temporary directory "
                                     ++ "must be specified in the environment variable `TEMP` (or `TMP`)."

/- Like `standaloneGoalFilename`, but gives an absolute path to a filename in the OS's temporary directory.-/
def temporaryStandaloneGoalFilepath (vg : VerificationGoal) : IO String := do
  let tempDir ← getTemporaryDirectory
  pure $ System.mkFilePath [tempDir, standaloneGoalFilename vg]


/- Generate the comment and other less semantically relevant options to set up a proof script. -/
def proofScriptPrelude (goalName : String) : Script :=
  let (_, _, cmds) := runSmtM IdGen.empty (do
    comment goalName
    setLogic Logic.all
    setProduceModels true)
  cmds

/- Check satisfiability with `goal` negated.  -/
def checkSatWithGoalNegated (goalName : String) (goal : SmtM (Term SmtSort.bool)) : SmtM Unit := do
  let p ← goal -- FIXME commands that appear before this do not appear in the final script =\
  checkSatAssuming [Smt.not p]
  exit


/- Write assert the negated goal and write out the resulting script
    of commands to a file. -/
def exportVerifyGoal
(outputDir : String)
(vg : VerificationGoal)
: IO Unit := do
  let preludeCmds := proofScriptPrelude vg.propName
  let (_, _, cmds) := runSmtM IdGen.empty (checkSatWithGoalNegated vg.propName vg.goal)
  let filePath := System.mkFilePath [outputDir, standaloneGoalFilename vg]
  let file ← IO.FS.Handle.mk filePath IO.FS.Mode.write
  preludeCmds.forM (λ c => file.putStr c.toLine)
  cmds.forM (λ c => file.putStr c.toLine)


def exportProverSession
(outputDir : String)
: IO ProverSession
:= do
  let initSmtM : SmtM Unit := pure ()
  let cmdRef <- IO.mkRef initSmtM
  pure { verifyGoal := exportVerifyGoal outputDir,
         sessionComplete := pure 0
       }


------------------------------------------------------------------------
-- Interactive session

-- | Information needed for interatively verifying goal.
structure InteractiveContext :=
(annFile : String)
-- ^ Annotation file (for error-reporting purposes)
(allGoalCounter : IO.Ref Nat)
-- ^ Counter for all goals (i.e., the total number)
(verifiedGoalCounter : IO.Ref Nat)
-- ^ Counter for all successfully verified goals.
(solverCommand : String)
-- ^ Command line contents, which when followed up a file name, can be executed
--   to see if the resulting script is satisfiable or not.



-- | Function to verify an SMT proposition is provable in the given
--   context and print the result to the user.
def verifyGoal
(goal : Smt.Term SmtSort.bool)
-- ^ Goal to verify
(propName : String)
-- ^ Name of proposition for reporting purposes.
: BlockVCG Unit := do
  let ctx ← read
  let smtCtx ← BlockVCGState.smtContext <$> get
  let goalIndex ← BlockVCGState.goalIndex <$> get
  let newGoal : VerificationEvent :=
    VerificationEvent.goal
    { fnName := ctx.llvmFunName,
      blockLbl := ctx.currentBlock,
      goalIndex := goalIndex,
      propName := propName,
      goal := do smtCtx; pure goal}
  modify (λ s => {s with
                  verificationEvents := newGoal :: s.verificationEvents,
                  goalIndex := s.goalIndex + 1})
  pure ()



-- | Function to verify an SMT proposition is provable in the given
-- | context and print the result to the user.
def interactiveVerifyGoal
(ictx : InteractiveContext)
(vg : VerificationGoal)
: IO Unit := do
  ictx.allGoalCounter.modify Nat.succ
  let smtFilePath ← temporaryStandaloneGoalFilepath vg
  let resultFilePath := smtFilePath ++ ".result"
  -- FIXME was stderr, fix with next Lean4 bump
  IO.print $ "  Verifying " ++ vg.propName ++ "... "
  -- FIXME, uncomment this line after next lean4 bump
  -- IO.stdout.flush
  let preludeCmds := proofScriptPrelude vg.propName
  let (_, _, cmds) := runSmtM IdGen.empty (checkSatWithGoalNegated vg.propName vg.goal)
  IO.FS.withFile smtFilePath IO.FS.Mode.write (λ file => do
    preludeCmds.forM (λ c => file.putStr c.toLine)
    cmds.forM (λ c => file.putStr c.toLine)
    file.flush)
  Galois.IO.system $ ictx.solverCommand++" "++smtFilePath++" > " ++resultFilePath
  let smtResult ← IO.FS.lines resultFilePath
  -- FIXME, this assumes the file has a single word in it essentially... might want to
  -- make it slightly more complicated if
  let printExportInstructions : IO Unit := (do
    let filePath := "<dir>" ++ [System.FilePath.pathSeparator].asString++(standaloneGoalFilename vg)
    -- FIXME print to stderr after next lean4 bump
    IO.println $ "    To see the output, run `reopt-vcg "++ictx.annFile++" --export <dir>`"
    IO.println $ "    The SMT query will be stored in "++filePath
    IO.println $ "    The default invocation of CVC4 for these queries is as follows:"
    IO.println $ "      `" ++ (String.intercalate " " ("cvc4"::defaultCVC4Args ++ [filePath]))++"`")
  match smtResult.get? 0 with
  | none => do
    -- FIXME print to stderr on next lean4 bump (these and all below printlns in this function)
    IO.println "ERROR"
    IO.println ""
    IO.println "    Verification failed: no response from the SMT solver was detected."
    printExportInstructions
  | some checkSatRes =>
    match parseCheckSatResult checkSatRes with
    | CheckSatResult.unsat => do
      ictx.verifiedGoalCounter.modify Nat.succ
      IO.println $ "OK"
    | CheckSatResult.sat => do
      IO.println $ "FAIL"
      IO.println $ "    Verification failed: the SMT query returned `sat`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unknown => do
      IO.println $ "FAIL"
      IO.println $ "    Verification failed: the SMT query returned `unknown`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unsupported => do
      IO.println $ "ERROR"
      IO.println $ "    Verification failed: the SMT query returned `unsupported`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unrecognized msg => do
      IO.println $ "ERROR"
      IO.println $ "    Verification failed: the SMT solver did not return a recognized response to `check-sat-assuming`."
      IO.println $ ""
      IO.println $ "    Response: "
      smtResult.forM IO.println
      IO.println $ ""
      IO.println $ ""
      IO.println $ "    This failure likely reflects a bug in reopt-vcg."
      IO.println $ ""
      printExportInstructions


def interactiveProverSession (annFile solverPath : String) (solverArgs : List String) : IO ProverSession := do
  -- Counter for all goals
  let allGoalCounter ← IO.mkRef 0
  -- Counter for goals successfully verified.
  let verifiedGoalCounter ← IO.mkRef 0
  -- Counter for errors
  let errorCounter ← IO.mkRef 0
  let doGoal : VerificationGoal → IO Unit :=
    (let solverCmd := String.intercalate " " (solverPath::solverArgs)
     let ictx : InteractiveContext:=
       { annFile := annFile,
         allGoalCounter := allGoalCounter,
         verifiedGoalCounter := verifiedGoalCounter,
         solverCommand := solverCmd
       }
     interactiveVerifyGoal ictx)
  let whenDone : IO UInt32 := (do
    let allCnt ← allGoalCounter.get
    let verCnt ← verifiedGoalCounter.get
    let errorCnt ← errorCounter.get
    let verSuccess := errorCnt == 0 && verCnt == allCnt
    if verSuccess then
      IO.println "Verification of all goals succeeded."
    else
      IO.println "Verification of all goals failed."
    IO.println $ "Verified "++(repr verCnt)++" out of "++(repr allCnt)++" generated goal(s)."
    when (errorCnt > 0) $
      IO.println $ "Encountered"++(repr errorCnt)++"error(s)."
    pure $ if verSuccess then 0 else 1)
  pure { verifyGoal := doGoal,
         sessionComplete := whenDone
       }

end ReoptVCG
