
import Galois.Data.SExp
import Galois.Init.Io
import ReoptVCG.ExitFlag
import ReoptVCG.SmtParser
import ReoptVCG.MCStdLib
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import SmtLib.Smt
import X86Semantics.Common

namespace ReoptVCG
open Std (RBMap)
open Smt hiding Array
universe u

abbrev GoalName := String

structure VerificationSession :=
  (verifyModule : VCGConfig → ModuleVerification → IO UInt32)


-- Data structure for registering verification goal info
-- (for interactive only, since export doesn't really do anything
--  with goals during execution except emit files).
structure GoalStats where
  /-- How many of each kind of goal failed -/
  okGoalCnt : RBMap GoalTag Nat Ord.compare
  /-- How many of each kind of goal failed to verify -/
  failGoalCnt : RBMap GoalTag Nat Ord.compare
  /-- For each kind of goal, what were the counts for each extra info seen for failures? -/
  failExtraInfoCnt : RBMap GoalTag (RBMap String Nat Ord.compare) Ord.compare
  /-- How many goals errored/failed for a given LLVM function name? -/
  fnBadGoalCnt : RBMap String Nat Ord.compare
  /-- How many of each kind of goal had an error during verification -/
  errorGoalCnt : RBMap GoalTag Nat Ord.compare
  /-- For each kind of goal, what were the counts for each extra info seen for errors? -/
  errorExtraInfoCnt : RBMap GoalTag (RBMap String Nat Ord.compare) Ord.compare
  /-- A terse description of what happened for mass data dumps of all activity -/
  results : Array VerificationResult

namespace GoalStats

def init : GoalStats :=
  {okGoalCnt := Std.RBMap.empty,
   failGoalCnt := Std.RBMap.empty,
   failExtraInfoCnt := Std.RBMap.empty,
   errorGoalCnt := Std.RBMap.empty,
   errorExtraInfoCnt := Std.RBMap.empty,
   fnBadGoalCnt := Std.RBMap.empty,
   results := #[]}

def addResult (gs : GoalStats) (vr : VerificationResult) : GoalStats :=
  let vg : VerificationGoal := vr.goal
  let logOk : GoalStats :=
      {gs with
       okGoalCnt :=
         let oks := gs.okGoalCnt
         oks.insert vg.tag (1 + (oks.findD vg.tag 0)),
       results := gs.results.push vr
      }
  let logFail : GoalStats :=
    {gs with
     failGoalCnt :=
       let fails := gs.failGoalCnt
       fails.insert vg.tag (1 + (fails.findD vg.tag 0)),
     failExtraInfoCnt := do
       let fails := gs.failExtraInfoCnt
       let mut tagFails := fails.findD vg.tag Std.RBMap.empty
       tagFails := tagFails.insert vg.extraInfo (1 + (tagFails.findD vg.extraInfo 0))
       fails.insert vg.tag tagFails,
     fnBadGoalCnt :=
      let fnFails := gs.fnBadGoalCnt
      fnFails.insert vg.loc.fnName (1 + (fnFails.findD vg.loc.fnName 0)),
     results := gs.results.push vr
    }
  let logError : GoalStats :=
    {gs with
     errorGoalCnt :=
       let errors := gs.errorGoalCnt
       errors.insert vg.tag (1 + (errors.findD vg.tag 0)),
     errorExtraInfoCnt := do
       let errors := gs.errorExtraInfoCnt
       let mut tagErrors := errors.findD vg.tag Std.RBMap.empty
       tagErrors := tagErrors.insert vg.extraInfo (1 + (tagErrors.findD vg.extraInfo 0))
       errors.insert vg.tag tagErrors,
     fnBadGoalCnt :=
      let fnFails := gs.fnBadGoalCnt
      fnFails.insert vg.loc.fnName (1 + (fnFails.findD vg.loc.fnName 0)),
     results := gs.results.push vr
    }
  match vr.result with
  | none => logError
  | some csr =>
    match csr with
    | CheckSatResult.unsat => logOk
    | CheckSatResult.sat => logFail
    | CheckSatResult.unknown => logFail
    | CheckSatResult.unsupported => logError
    | CheckSatResult.unrecognized msg => logError


end GoalStats

-- Data for counting function/block level errors that occur during VC generation
structure VCStats where
  /-- How many functions did we analyze for VC gen? -/
  fnCnt : Nat
  /-- How many errors were encoutered during VC gen?  -/
  errCnt : Nat
  /-- How many (module or block) errors did each function have during VC gen?  -/
  fnErrCnt : RBMap String Nat Ord.compare
  /-- What warnings were raised during VC gen?  -/
  warnings : Array VerificationWarning
  /-- Module errors that were encountered during VC  -/
  moduleErrs : Array ModuleError
  /-- How many errors of each kind of ModuleError did we encounter?  -/
  moduleErrCnt : RBMap ModuleErrorTag Nat Ord.compare
  /-- For each ModuleError kind and additional info, how many times did we see that combination?  -/
  moduleErrExtraInfoCnt : RBMap ModuleErrorTag (RBMap String Nat Ord.compare) Ord.compare
  /-- Block errors that were encountered during VC  -/
  blockErrs : Array BlockError
  /-- How many errors of each kind of BlockError did we encounter?  -/
  blockErrCnt : RBMap BlockErrorTag Nat Ord.compare
  /-- For each BlockError kind and additional info, how many times did we see that combination? -/
  blockErrExtraInfoCnt : RBMap BlockErrorTag (RBMap String Nat Ord.compare) Ord.compare


namespace VCStats

def init : VCStats :=
  {fnCnt := 0,
   errCnt := 0,
   fnErrCnt := Std.RBMap.empty,
   warnings := #[],
   moduleErrs := #[],
   moduleErrCnt := Std.RBMap.empty,
   moduleErrExtraInfoCnt := Std.RBMap.empty,
   blockErrs := #[]
   blockErrCnt := Std.RBMap.empty,
   blockErrExtraInfoCnt := Std.RBMap.empty}

def addModuleError (stats : VCStats) (err : ModuleError) : VCStats := do
  let mut stats := stats
  -- If there was an associated function name for this module error,
  -- increaser the count for that function.
  match err.loc.fnName with
  | none => pure ()
  | some fnName => do
    stats := {stats with
              fnErrCnt :=
                let errCnt := stats.fnErrCnt
                errCnt.insert fnName (1 + (errCnt.findD fnName 0))}
  pure {stats with
   errCnt := 1 + stats.errCnt,
   moduleErrs := stats.moduleErrs.push err,
   moduleErrCnt :=
     let errors := stats.moduleErrCnt
     errors.insert err.tag (1 + (errors.findD err.tag 0)),
   moduleErrExtraInfoCnt := do
     let errors := stats.moduleErrExtraInfoCnt
     let mut tagErrors := errors.findD err.tag Std.RBMap.empty
     tagErrors := tagErrors.insert err.extraInfo (1 + (tagErrors.findD err.extraInfo 0))
     errors.insert err.tag tagErrors
  }

def addBlockError (stats : VCStats) (err : BlockError) : VCStats := do
  pure {stats with
   errCnt := 1 + stats.errCnt,
   blockErrs := stats.blockErrs.push err,
   fnErrCnt :=
     let errCnt := stats.fnErrCnt
     errCnt.insert err.loc.fnName (1 + (errCnt.findD err.loc.fnName 0)),
   blockErrCnt :=
     let errors := stats.blockErrCnt
     errors.insert err.tag (1 + (errors.findD err.tag 0)),
   blockErrExtraInfoCnt := do
     let errors := stats.blockErrExtraInfoCnt
     let mut tagErrors := errors.findD err.tag Std.RBMap.empty
     tagErrors := tagErrors.insert err.extraInfo (1 + (tagErrors.findD err.extraInfo 0))
     errors.insert err.tag tagErrors
  }

def addWarning (stats : VCStats) (w : VerificationWarning) : VCStats := do
  pure {stats with warnings := stats.warnings.push w}

end VCStats



def defaultCVC4Args : List String :=
-- N.B., as of CVC4 46591b1c92fc9ecd4a0997242030a1a48166301b the `--arrays-exp` flag
-- enables `--fmf-bound` by default to help with some `sat` queries; it shouldn't affect
-- `unsat` queries allegedly but appears to currently (i.e., some which should produce
-- `unsat` instead produce `unknown`) so we manually pass the `--no-fmf-bound` flag to
-- avoid the `unknown`s.
["--lang=smt2", "--arrays-exp", "--no-fmf-bound", "--incremental"]

def defaultCVC4Cmd : String :=
  String.intercalate " " ("cvc4"::defaultCVC4Args)

/- Abstracts out the _specifics_ of how certain BlockExpr terms
    should be emitted as SMT terms, so that the underlying SMT
    architecture can generate these ahead of time in whatever way is
    appropriate and then simply parameterize SMT generation of
    precondition expressions accordingly. -/
class BlockExprEnv (α : Type u) :=
(initGPReg64 : α → x86.reg64 → Term SmtSort.bv64)
(initFlag : α → x86.flag → Term SmtSort.bool)
(fnStartRegState : α → x86.reg64 → Term SmtSort.bv64)
(beforeCallRegState : α → x86.reg64 → Term SmtSort.bv64)
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

def beforeCallRegState (r : x86.reg64) : Term SmtSort.bv64 :=
e.state.mcPreCallRegs.get_reg64 r

def readMem (w:WordSize) (addr : x86.vcg.memaddr) : Term w.sort :=
(e.context.mcStdLib.memOps w).readMem e.state.mcCurMem addr

end BlockVCGExprEnv

instance BlockVCGExprEnv.isBlockExprEnv : BlockExprEnv BlockVCGExprEnv :=
{initGPReg64 := BlockVCGExprEnv.initGPReg64,
 initFlag    := BlockVCGExprEnv.initFlag,
 fnStartRegState := BlockVCGExprEnv.fnStartRegState,
 beforeCallRegState := BlockVCGExprEnv.beforeCallRegState,
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
| _, beforeCallGPReg64 r => SExp.list [SExp.atom "before_call", SExp.atom r.name]
| _, mcStack a w =>
  SExp.list [SExp.atom "mcstack",
             toSExp a,
             SExp.list [SExp.atom "_", SExp.atom "BitVec", SExp.atom (reprStr w.bits)]
            ]
| _, llvmVar nm tp => SExp.list [SExp.atom "llvm", SExp.atom (ppLLVMIdent nm)]
| _, smtBinOp ident e1 e2 => SExp.list [ toSExpr ident, toSExp e1, toSExp e2]
| _, smtBool b => SExp.atom (if b then "true" else "false")
| _, bvDecimal n width => SExp.list [SExp.atom "_", SExp.atom ("bv"++(reprStr n)), SExp.atom (reprStr width)]

def toString : ∀ {tp : SmtSort}, BlockExpr tp → String
| _, e => (BlockExpr.toSExp e).toString

section


open Smt.Raw.Term (app ident)
open Smt.Raw.Ident (builtin)

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
| _, beforeCallGPReg64 r => pure $ BlockExprEnv.beforeCallRegState env r
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
| _, smtBinOp i e1 e2 => do
  let t1 ← toSmt env e1
  let t2 ← toSmt env e2
  -- FIXME
  pure $ app (app (ident (builtin i)) t1) t2
| _, smtBool b => do
  pure $ if b then Smt.true else Smt.false
| _, bvDecimal n width => pure $ Smt.bvimm width n

end

end BlockExpr

/- Converts a BlockExpr into an SMT term in the BlockVCG context. -/
def evalBlockExpr {tp : SmtSort} (evalVar : LLVM.Ident → Option (Sigma Term)) (expr : BlockExpr tp) : BlockVCG (Term tp) := do
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
      if (← System.FilePath.isDir dir)
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
def temporaryStandaloneGoalFilepath (vg : VerificationGoal) : IO System.FilePath := do
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
def exportDoGoal
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


------------------------------------------------------------------------
-- Interactive session

-- | Information needed for interatively verifying goal.
structure InteractiveContext :=
(annFile : String)
-- ^ Annotation file (for error-reporting purposes)
(onResult : (res : VerificationResult) → IO Unit)
-- ^ Action to run when a goal is completed
(results : IO.Ref (Array VerificationResult))
-- ^ Results from trying to verify goals.
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
  unless List.elem tag ctx.mcModuleVCGContext.ignoredGoalTags do
    let newGoal : VerificationGoal :=
      { loc := {fnName := ctx.llvmFnName,
                blockLbl := ctx.currentBlock,
                llvmInstrIdx := st.llvmInstrIndex,
                mcAddr := st.mcCurAddr},
        index := st.goals.size,
        tag := tag,
        extraInfo := extraInfo,
        goal := do st.smtContext; pure goal}
    modify (λ s => {s with
                    goals := s.goals.push newGoal})

  pure ()


-- | Function to verify an SMT proposition is provable in the given
-- | context and print the result to the user.
def interactiveDoGoal
(ictx : InteractiveContext)
(cfg : VCGConfig)
(vg : VerificationGoal)
: IO Unit := do
  let smtFilePath ← temporaryStandaloneGoalFilepath vg
  let resultFilePath := smtFilePath.withExtension "result"
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
  Galois.IO.system $ ictx.solverCommand++" "++smtFilePath.toString++" > " ++resultFilePath.toString
  let smtResult ← IO.FS.lines resultFilePath
  -- FIXME, this assumes the file has a single word in it essentially... might want to
  -- make it slightly more complicated if
  let printExportInstructions : IO Unit := do
    let filePath := "<dir>" ++ [System.FilePath.pathSeparator].asString++(standaloneGoalFilename vg)
    -- FIXME print to stderr after next lean4 bump
    IO.println $ "    To see the output, run `reopt-vcg "++ictx.annFile++" --export <dir>`"
    IO.println $ "    The SMT query will be stored in "++filePath
    IO.println $ "    The default invocation of CVC4 for these queries is as follows:"
    IO.println $ "      `" ++(defaultCVC4Cmd++" "++filePath)++"`"
  let extraInfo := if cfg.verbose then "" else "    "++vg.fullDescription++"\n"
  match smtResult.get? 0 with
  | none => do
    -- FIXME print to stderr on next lean4 bump (these and all below printlns in this function)
    if !cfg.verbose then do
      -- In verbose mode we want `FAIL` or `ERROR` on the same line as the preceding text, but
      -- in non-verbose mode the newline makes a nice break from the stream of periods.
      IO.println $ ""
    IO.println "ERROR"
    IO.print extraInfo
    IO.println "    Verification failed: no response from the SMT solver was detected."
    ictx.onResult ⟨vg, none⟩
  | some checkSatRes =>
    let res ← parseCheckSatResult checkSatRes
    ictx.onResult ⟨vg, some res⟩
    match res with
    | CheckSatResult.unsat => do
      if cfg.verbose then do
        IO.println "OK"
    | CheckSatResult.sat => do
      if !cfg.verbose then do
        IO.println $ ""
      IO.println $ "FAIL"
      IO.print extraInfo
      IO.println $ "    Verification failed: the SMT query returned `sat`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unknown => do
      if !cfg.verbose then do
        IO.println $ ""
      IO.println $ "FAIL"
      IO.print extraInfo
      IO.println $ "    Verification failed: the SMT query returned `unknown`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unsupported => do
      if !cfg.verbose then do
        IO.println $ ""
      IO.println $ "ERROR"
      IO.print extraInfo
      IO.println $ "    Verification failed: the SMT query returned `unsupported`"
      IO.println $ ""
      printExportInstructions
    | CheckSatResult.unrecognized msg => do
      if !cfg.verbose then do
        IO.println $ ""
      IO.println $ "ERROR"
      IO.print extraInfo
      IO.println $ "    Verification failed: the SMT solver did not return a recognized response to `check-sat-assuming`."
      IO.println $ ""
      IO.println $ "    Response: "
      smtResult.forM IO.println
      IO.println $ ""
      IO.println $ ""
      IO.println $ "    This failure likely reflects a bug in reopt-vcg."
      IO.println $ ""
      printExportInstructions


-- Generic module verification code, parameterized by how to handle a VerificationGoal
-- and how to report a summary and return
def verifyModule'
  (doGoal : VerificationGoal → IO Unit)
  (reportSummary : VCStats → IO UInt32)
  (mv : ModuleVerification)
  : IO UInt32 := do
  let mut vcStats := VCStats.init
  -- Register module errors
  for mErr in mv.errors do
    vcStats := vcStats.addModuleError mErr
  -- Function VC loop -- iterate through each function being verified
  for fv in mv.fnVCs do
    vcStats := {vcStats with fnCnt := vcStats.fnCnt + 1}
    -- Register block errors
    for bErr in fv.blockErrors do
      vcStats := vcStats.addBlockError bErr
    -- Handle any (block) verification content for this function
    for bv in fv.blockVCs do
      -- Log the warnings for this block
      for w in bv.warnings do
        vcStats := vcStats.addWarning w
      -- Handle each goal from the block
      for g in bv.goals do
        doGoal g
  -- Now that we're done, report to the user what happened and return
  reportSummary vcStats

private def printVCStats (stats : VCStats) : IO Unit := do
  let indent := "    "
  -- Dislpay warnings encountered during VC
  if stats.warnings.size > 0 then do
    IO.println $ ""
    IO.println $ "======================= "++(toString stats.warnings.size)++" VC GENERATION WARNINGS ======================="
    for w in stats.warnings do
      IO.println $ w.loc.pp ++ ": " ++ w.msg
  -- Dislpay errors encountered during VC
  if stats.moduleErrs.size > 0 || stats.blockErrs.size > 0 then do
    IO.println $ ""
    IO.println $ "======================= "++(toString (stats.moduleErrs.size + stats.blockErrs.size))++" VC GENERATION ERRORS  ======================="
    for mErr in stats.moduleErrs do
      IO.println $ mErr.pp
    for bErr in stats.blockErrs do
      IO.println $ bErr.pp
  let printExtraInfo : Bool → Nat → String → IO Unit :=
    λ oneCategory n info =>
      if oneCategory && info == ""
      then pure () -- if there's one empty category, don't print it as a subcategory... that looks silly
      else if info == ""
      then IO.println $ indent++"- ("++(repr n)++") no additional information"
      else IO.println $ indent++"- ("++(repr n)++") "++info
  -- Summarize module and block errors by error type
  if stats.moduleErrCnt.size > 0 || stats.blockErrCnt.size > 0 then do
    let mCnt : Nat := stats.moduleErrCnt.fold (init := 0) (λ acc _fnName cnt => acc + cnt)
    let bCnt : Nat := stats.blockErrCnt.fold (init := 0) (λ acc _fnName cnt => acc + cnt)
    -- Summarize module errors by error type
    IO.println $ ""
    IO.println $ "======================= VC GENERATION ERROR SUMMARY ======================="
    for (tag, tagCnt) in stats.moduleErrCnt.toList do -- FIXME remote .toList after Lean4 bump
      IO.println $ "* ("++(repr tagCnt)++") [module] "++tag.description
      let tagMap := stats.moduleErrExtraInfoCnt.findD tag Std.RBMap.empty
      for (extraInfo, n) in tagMap.toList do -- FIXME remove toList next lean bump
        printExtraInfo (tagMap.size > 1) n extraInfo
    -- Summarize block errors by error type
    for (tag, tagCnt) in stats.blockErrCnt.toList do -- FIXME remote .toList after Lean4 bump
      IO.println $ "* ("++(repr tagCnt)++") [block] "++tag.description
      let tagMap := stats.blockErrExtraInfoCnt.findD tag Std.RBMap.empty
      for (extraInfo, n) in tagMap.toList do -- FIXME remove toList next lean bump
        printExtraInfo (tagMap.size > 1) n extraInfo
  IO.println $ ""
  -- Report how many functions had no errors
  if stats.fnErrCnt.size == 0 then do
    IO.println $ "All " ++ (repr stats.fnCnt) ++ " functions were assigned verification conditions without error."
  else do
    IO.println $ (repr (stats.fnCnt - stats.fnErrCnt.size)) ++ " out of "
                 ++ (repr stats.fnCnt) ++ " functions were assigned verification conditions without error."


private def printGoalStats (stats : GoalStats) : IO Unit := do
  let indent := "    "
  IO.println $ ""
  IO.println $ "====================== GOAL VERIFICATION SUMMARY ======================="
  let successes : Nat := stats.okGoalCnt.fold    (init := 0) (λ acc _ cnt => acc + cnt)
  let fails     : Nat := stats.failGoalCnt.fold  (init := 0) (λ acc _ cnt => acc + cnt)
  let errs      : Nat := stats.errorGoalCnt.fold (init := 0) (λ acc _ cnt => acc + cnt)
  let failsAndErrs : Nat := fails + errs
  if failsAndErrs == 0 then do
    IO.println $ "All "++(repr successes)++" generated verification goals successfully proven."
  else do
    IO.println $ (repr successes)++" out of "++(repr (successes + failsAndErrs))
                 ++" generated verification goals successfully proven."
  let printExtraInfo : Bool → Nat → String → IO Unit :=
    λ oneCategory n info =>
      if oneCategory && info == ""
      then pure () -- if there's one empty category, don't print it as a subcategory... that looks silly
      else if info == ""
      then IO.println $ indent++"- ("++(repr n)++") no additional information"
      else IO.println $ indent++"- ("++(repr n)++") "++info
  let printGoalMaps : RBMap GoalTag Nat Ord.compare → RBMap GoalTag (RBMap String Nat Ord.compare) Ord.compare → IO Unit :=
    λ cntMap extraInfoMap => do
      for (tag, tagCnt) in cntMap.toList do -- FIXME remote .toList after Lean4 bump
      IO.println $ "* ("++(repr tagCnt)++") "++tag.description
      let tagMap := extraInfoMap.findD tag Std.RBMap.empty
      for (extraInfo, n) in tagMap.toList do -- FIXME remove toList next lean bump
        printExtraInfo (tagMap.size > 1) n extraInfo
  if fails > 0 then do
    IO.println $ ""
    IO.println $ (repr fails)++" goals failed to be verified:"
    printGoalMaps stats.failGoalCnt stats.failExtraInfoCnt
  if errs > 0 then do
    IO.println $ ""
    IO.println $ (repr fails)++" goals resulted in errors during verification:"
    printGoalMaps stats.errorGoalCnt stats.errorExtraInfoCnt

def mkGoalStats (results : Array VerificationResult) : IO GoalStats := do
  let mut stats : GoalStats := GoalStats.init
  for r in results do
    stats := stats.addResult r
  pure stats


/--
Based on whether a JSON output is specified in the configuration, returns an
action to run when a verification result is known.

`logStrategy` itself is an `IO` as it may need to set up a file handle or some
such output.

Currently we use the `IO.FS.Handle` API, which automatically closes the handle
when it leaves scope, so there is no need for a final action, though it could be
configured here if needed.
-/
def logStrategy (cfg : VCGConfig) : IO (VerificationResult → IO Unit) := do
  match cfg.getJsonOut? with
  | none => pure (λ res => pure ())
  | some jsonOutFile => do
    let file ← IO.FS.Handle.mk jsonOutFile IO.FS.Mode.write
    -- render each goal as a single line of JSON
    let resToString := λ (vr : VerificationResult) => " ".intercalate $ (toString $ Lean.toJson vr).splitOn "\n"
    IO.println $ "Verification results stored in `" ++ jsonOutFile ++"` (one JSON object for each goal, one per line)."
    return (λ res => do
      file.putStrLn (resToString res)
      file.flush
    )


def interactiveVerificationSession (annFile solverPath : String) (solverArgs : List String) : IO VerificationSession := do
  let results : IO.Ref (Array VerificationResult) ← IO.mkRef #[]
  -- -- Counter for errors
  let interactiveReportSummary : VCGConfig → VCStats → IO UInt32 :=
    λ cfg vcStats => do
      printVCStats vcStats
      let vrs ← results.get
      let gStats ← mkGoalStats vrs
      printGoalStats gStats
      let exitStatus : UInt32 :=
        (if vcStats.errCnt > 0 then ExitFlag.generationError else 0b0)
        ||| (if gStats.failGoalCnt.size > 0 then ExitFlag.verificationFailure else 0b0)
        ||| (if gStats.errorGoalCnt.size > 0 then ExitFlag.verificationError else 0b0)
      pure exitStatus
  pure { verifyModule := λ cfg modv => do
    let applyLogStrategy ← logStrategy cfg
    let ictx : InteractiveContext := {
      annFile := annFile,
      onResult := λ v => do
        results.modify (λ rs => rs.push v)
        applyLogStrategy v,
      results := results,
      solverCommand := String.intercalate " " (solverPath::solverArgs)
    }
    verifyModule' (interactiveDoGoal ictx cfg) (interactiveReportSummary cfg) modv
  }


def exportVerificationSession (outDir : String) : IO VerificationSession := do
  let fileCntRef ← IO.mkRef 0
  let interactiveReportSummary : VCGConfig → VCStats → IO UInt32 :=
    λ cfg vcStats => do
      printVCStats vcStats
      let fileCnt ← fileCntRef.get
      IO.println $ (repr fileCnt)++" verification condition .smt2 files generated in directory `" ++ outDir ++ "`."
      pure (if vcStats.errCnt > 0
            then ExitFlag.generationError
            else 0)
  pure { verifyModule := λ cfg => verifyModule' (exportDoGoal outDir fileCntRef cfg) (interactiveReportSummary cfg)}


end ReoptVCG
