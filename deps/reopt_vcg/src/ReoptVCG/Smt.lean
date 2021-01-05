
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


-- Did the prover session complete successfully or fail in some way?
structure ProverSessionResult :=
  (success : Bool)
  (printSummary : IO Unit)
  (printFailures : IO Unit)

structure ProverSession :=
  (verifyGoal : VCGConfig → VerificationGoal → IO Unit)
  (sessionComplete : IO ProverSessionResult)


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
| LLVM.Ident.anon n => "%"++(reprStr n)

def toSExp : ∀ {tp : SmtSort}, BlockExpr tp → SExp String
| _, stackHigh => SExp.atom "stack_high"
| _, initGPReg64 r => SExp.atom r.name
| _, initFlag r    => SExp.atom r.name
| _, fnStartGPReg64 r => SExp.list [SExp.atom "fnstart", SExp.atom r.name]
| _, mcStack a w =>
  SExp.list [SExp.atom "mcstack",
             toSExp a,
             SExp.list [SExp.atom "_", SExp.atom "BitVec", SExp.atom (reprStr w.bits)]
            ]
| _, llvmVar nm tp => SExp.list [SExp.atom "llvm", SExp.atom (ppLLVMIdent nm)]
| _, eq e1 e2 => SExp.list [SExp.atom "=", toSExp e1, toSExp e2]
| _, bvAdd e1 e2 => SExp.list [SExp.atom "bvadd", toSExp e1, toSExp e2]
| _, bvSub e1 e2 => SExp.list [SExp.atom "bvsub", toSExp e1, toSExp e2]
| _, bvDecimal n width => SExp.list [SExp.atom "_", SExp.atom ("bv"++(reprStr n)), SExp.atom (reprStr width)]

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


def standaloneGoalFilename (vg : VerificationGoal) : String :=
  vg.loc.fnName ++ "_" ++ (ppBlockLabel vg.loc.blockLbl) ++ "_" ++ vg.index.repr ++ ".smt2"

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
def checkSatWithGoalNegated (goal : SmtM (Term SmtSort.bool)) : SmtM Unit := do
  let p ← goal
  checkSatAssuming [Smt.not p]
  exit


/- Write assert the negated goal and write out the resulting script
    of commands to a file. -/
def exportVerifyGoal
(outputDir : String)
(fileCnt : IO.Ref Nat)
(cfg : VCGConfig)
(vg : VerificationGoal)
: IO Unit := do
  let preludeCmds := proofScriptPrelude vg.fullDescription
  let (_, _, cmds) := runSmtM IdGen.empty (checkSatWithGoalNegated vg.goal)
  let filePath := System.mkFilePath [outputDir, standaloneGoalFilename vg]
  let file ← IO.FS.Handle.mk filePath IO.FS.Mode.write
  preludeCmds.forM (λ c => file.putStr c.toLine)
  cmds.forM (λ c => file.putStr c.toLine)
  let stdout ← IO.getStdout
  stdout.putStr "."
  stdout.flush
  fileCnt.modify Nat.succ


def exportProverSession
(outputDir : String)
: IO ProverSession
:= do
  let fileCnt <- IO.mkRef 0
  pure { verifyGoal := exportVerifyGoal outputDir fileCnt,
         sessionComplete := pure {success := true,
                                  printSummary := do
                                    let n ← fileCnt.get
                                    IO.println $ (repr n)++ " verification condition files generated in `"++outputDir++"`.",
                                  printFailures := pure ()}
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
(fnCounter : IO.Ref (Std.RBMap String Nat (λ x y => x < y)))
-- ^ Counter for each function name, i.e., how many failures/errors were encountered in that function
(goalFailures : IO.Ref (Std.RBMap GoalTag (Std.RBMap String Nat (λ x y => x < y)) GoalTag.lt))
-- ^ Counter for each failing goal by property.
(goalErrors : IO.Ref Nat)
-- ^ Counter for each erroring goal by property.
(solverCommand : String)
-- ^ Command line contents, which when followed up a file name, can be executed
--   to see if the resulting script is satisfiable or not.



-- | Function to verify an SMT proposition is provable in the given
--   context and print the result to the user.
def verifyGoal
(tag : GoalTag)
-- ^ Goal to verify
(extraInfo : String)
(goal : Smt.Term SmtSort.bool)
-- ^ Name of proposition for reporting purposes.
: BlockVCG Unit := do
  let ctx ← read
  let st ← get
  let newGoal : VerificationEvent :=
    VerificationEvent.goal
    { loc := {fnName := ctx.llvmFunName,
              blockLbl := ctx.currentBlock,
              llvmInstrIdx := st.llvmInstrIndex,
              mcAddr := st.mcCurAddr},
      index := st.goalIndex,
      tag := tag,
      extraInfo := extraInfo,
      goal := do st.smtContext; pure goal}
  modify (λ s => {s with
                  verificationEvents := newGoal :: s.verificationEvents,
                  goalIndex := s.goalIndex + 1})
  pure ()



-- | Function to verify an SMT proposition is provable in the given
-- | context and print the result to the user.
def interactiveVerifyGoal
(ictx : InteractiveContext)
(cfg : VCGConfig)
(vg : VerificationGoal)
: IO Unit := do
  ictx.allGoalCounter.modify Nat.succ
  let smtFilePath ← temporaryStandaloneGoalFilepath vg
  let resultFilePath := smtFilePath ++ ".result"
  -- FIXME was stderr, fix with next Lean4 bump
  if cfg.verbose then do
    let stdout ← IO.getStdout
    stdout.putStr $ "  Verifying " ++ vg.fullDescription ++ "... "
    stdout.flush
  else do
    let stdout ← IO.getStdout
    stdout.putStr "."
    stdout.flush
  -- FIXME, uncomment this line after next lean4 bump
  -- IO.stdout.flush
  let preludeCmds := proofScriptPrelude vg.fullDescription
  let (_, _, cmds) := runSmtM IdGen.empty (checkSatWithGoalNegated vg.goal)
  IO.FS.withFile smtFilePath IO.FS.Mode.write (λ file => do
    preludeCmds.forM (λ c => file.putStr c.toLine)
    cmds.forM (λ c => file.putStr c.toLine)
    file.flush)
  Galois.IO.system $ ictx.solverCommand++" "++smtFilePath++" > " ++resultFilePath
  let smtResult ← IO.FS.lines resultFilePath
  -- FIXME, this assumes the file has a single word in it essentially... might want to
  -- make it slightly more complicated if
  let printExportInstructions : IO Unit := do
    let filePath := "<dir>" ++ [System.FilePath.pathSeparator].asString++(standaloneGoalFilename vg)
    -- FIXME print to stderr after next lean4 bump
    IO.println $ "    To see the output, run `reopt-vcg "++ictx.annFile++" --export <dir>`"
    IO.println $ "    The SMT query will be stored in "++filePath
    IO.println $ "    The default invocation of CVC4 for these queries is as follows:"
    IO.println $ "      `" ++ (String.intercalate " " ("cvc4"::defaultCVC4Args ++ [filePath]))++"`"
  let registerFailure : IO Unit := do
    printExportInstructions
    ictx.goalFailures.modify 
      λ m => let tagMap := m.findD vg.tag Std.RBMap.empty
             let count := tagMap.findD vg.extraInfo 0
             m.insert vg.tag (tagMap.insert vg.extraInfo (count + 1))
    ictx.fnCounter.modify
      λ m => m.insert vg.loc.fnName ((m.findD vg.loc.fnName 0) + 1)
  let registerError : IO Unit := do
    printExportInstructions
    ictx.goalErrors.modify Nat.succ
    ictx.fnCounter.modify
      λ m => m.insert vg.loc.fnName ((m.findD vg.loc.fnName 0) + 1)
  match smtResult.get? 0 with
  | none => do
    -- FIXME print to stderr on next lean4 bump (these and all below printlns in this function)
    IO.println "ERROR"
    IO.println ""
    IO.println "    Verification failed: no response from the SMT solver was detected."
    registerError
  | some checkSatRes =>
    match parseCheckSatResult checkSatRes with
    | CheckSatResult.unsat => do
      ictx.verifiedGoalCounter.modify Nat.succ
      ictx.fnCounter.modify
        λ m => m.insert vg.loc.fnName ((m.findD vg.loc.fnName 0))
      if cfg.verbose then do
        IO.println "OK"
    | CheckSatResult.sat => do
      IO.println $ ""
      IO.println $ "FAIL"
      IO.println $ "    Verification failed: the SMT query returned `sat`"
      IO.println $ ""
      registerFailure
    | CheckSatResult.unknown => do
      IO.println $ ""
      IO.println $ "FAIL"
      IO.println $ "    Verification failed: the SMT query returned `unknown`"
      IO.println $ ""
      registerFailure
    | CheckSatResult.unsupported => do
      IO.println $ ""
      IO.println $ "ERROR"
      IO.println $ "    Verification failed: the SMT query returned `unsupported`"
      IO.println $ ""
      registerError
    | CheckSatResult.unrecognized msg => do
      IO.println $ ""
      IO.println $ "ERROR"
      IO.println $ "    Verification failed: the SMT solver did not return a recognized response to `check-sat-assuming`."
      IO.println $ ""
      IO.println $ "    Response: "
      smtResult.forM IO.println
      IO.println $ ""
      IO.println $ ""
      IO.println $ "    This failure likely reflects a bug in reopt-vcg."
      IO.println $ ""
      registerError

private def printFailures (failures : Std.RBMap GoalTag (Std.RBMap String Nat (λ x y => x < y)) GoalTag.lt) : IO Unit := do
  let cnt := 0
  for (_, entries) in failures.toList do -- FIXME remote toList next bump
    for (extraInfo, n) in entries.toList do -- FIXME remote toList next bump
      cnt := cnt + n
  IO.println $ ""
  IO.println "====================== FAILURES ======================="
  IO.println $ ""
  IO.println $ "Failed to verify "++(repr cnt)++" goal(s):"
  let indent := "  "
  for (tag, entries) in failures.toList do -- FIXME remote toList next bump
    let pCnt : Nat := 0
    let pDetails : List (Nat × String) := []
    for (extraInfo, n) in entries.toList do -- FIXME remote toList next bump
      pCnt := pCnt + n
      pDetails :=  (n, extraInfo)::pDetails
    let printInfo : Nat → String → IO Unit :=
      λ n info => if info == ""
                  then IO.println $ indent++indent++"- ("++(repr n)++") no additional information"
                  else IO.println $ indent++indent++"- ("++(repr n)++") "++info
    IO.println $ indent++"* ("++(repr pCnt)++") "++tag.description
    match pDetails with
    | (n, info) :: [] =>
      if info == ""
      -- if there was only a single, empty category, then do not print anything, there are no additional details
      then pure ()
      else printInfo n info
    | ds =>
      for (n, info) in ds do
        printInfo n info
 

def interactiveProverSession (annFile solverPath : String) (solverArgs : List String) : IO ProverSession := do
  -- Counter for all goals
  let allGoalCounter ← IO.mkRef 0
  -- Counter for goals successfully verified.
  let verifiedGoalCounter ← IO.mkRef 0
  -- Counter for errors
  let fnCounterRef ← IO.mkRef Std.RBMap.empty
  let failuresRef ← IO.mkRef Std.RBMap.empty
  let errorsRef ← IO.mkRef 0
  let doGoal : VCGConfig → VerificationGoal → IO Unit :=
     interactiveVerifyGoal {
        annFile := annFile,
        allGoalCounter := allGoalCounter,
        verifiedGoalCounter := verifiedGoalCounter,
        fnCounter := fnCounterRef,
        goalFailures := failuresRef,
        goalErrors := errorsRef,
        solverCommand := String.intercalate " " (solverPath::solverArgs)
      }
  let whenDone : IO ProverSessionResult := do
    let allCnt ← allGoalCounter.get
    let verCnt ← verifiedGoalCounter.get
    let fnCounter ← fnCounterRef.get
    let failures ← failuresRef.get
    let errors ← errorsRef.get
    let fnWithIssues := fnCounter.fold (init := 0) (λ acc _ fnCnt => acc + (if fnCnt > 0 then 1 else 0))
    let verSuccess := failures.size == 0 && errors == 0 && verCnt == allCnt
    let printSummary : IO Unit := do
      IO.println ""
      IO.println "=================== SOLVER  SUMMARY ==================="
      IO.println ""
      if verSuccess then
        IO.println "Verification of all goals succeeded."
      else
        IO.println "Verification of all goals failed."
      IO.println $ "Verified "++(repr verCnt)++" out of "++(repr allCnt)++" generated goals."
      IO.println $ (repr (fnCounter.size - fnWithIssues))++" out of " ++ (repr fnCounter.size)
                   ++ " functions with verification conditions passed all SMT checks."
    let printFailures : IO Unit := do
      if (failures.size > 0) then
        printFailures failures
      if (errors > 0) then
        IO.println $ "Encountered "++(repr errors)++" error(s) while interacting with SMT solver."
    pure $ {success := verSuccess,
            printSummary := printSummary,
            printFailures := printFailures}
  pure { verifyGoal := doGoal,
         sessionComplete := whenDone
       }

end ReoptVCG
