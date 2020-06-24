
import Galois.Data.SExp
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

def toSExp : ∀ {tp : sort}, BlockExpr tp → SExp String
| _, _ => SExp.atom "TODO BlockExpr.toSExp"

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
let (_, _, cmds) := 
  runsmtM 0 (setLogic Raw.logic.all
            *> setOption (Raw.option.produceModels true)
            *> smtCtx
            *> checkSatAssuming [negatedGoal]
            *> exit);
let filePath := outputDir ++ [System.FilePath.pathSeparator].asString ++ (standaloneGoalFilename fnName blockLabel cnt);
file ← IO.FS.Handle.mk filePath IO.FS.Mode.write;
-- TODO make these actual commands in our Lean4 SMT namespace
file.putStr ("; "++ goalName ++ "\n");
cmds.forM $ λ c => file.putStr $ (toString (toSExpr c)) ++ "\n"


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
  {addSMTCallback := λ action => cmdRef.modify (λ cmds => cmds *> action),
   addCommandCallback := λ cmd => cmdRef.modify (λ cmds => cmds *> liftCommand cmd),
   proveFalseCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef p msg,
   proveTrueCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef (SMT.not p) msg,
   blockErrorCallback := λ i a msg =>
    -- FIXME stderr and other handles are in Lean4, fix when we bump next
    IO.println $ "Error: " ++ renderMCInstError fnName blockLabel i a msg
  }


end ReoptVCG
