

import ReoptVCG.SMTParser
import ReoptVCG.MCStdLib
import ReoptVCG.Types
import ReoptVCG.WordSize
import SMTLIB.Syntax

namespace ReoptVCG
open SMT


/-- Abstracts out the _specifics_ of how certain BlockExpr terms
    should be emitted as SMT terms, so that the underlying SMT
    architecture can generate these ahead of time in whatever way is
    appropriate and then simply parameterize SMT generation of
    precondition expressions accordingly. --/
structure BlockExprContext :=
(stackHigh : term sort.bv64)
(initGPReg64 : x86.reg64 → term sort.bv64)
(memory : term (sort.array sort.bv64 sort.bv8))
(fnStartRegState : x86.reg64 → term sort.bv64)
(regState : x86.reg64 → term sort.bv64)
(phiVarMap : ∀(nm:String) (tp:sort), term tp)
(mcMemOps : ∀(w : WordSize), x86.vcg.SupportedMemType w.sort)

namespace BlockExpr

-- Converts an Expr into an SMT term, cf. `evalPrecondition`
def toSMT (ctx:BlockExprContext) : ∀ {tp : sort}, BlockExpr tp → term tp
| _, stackHigh => ctx.stackHigh
| _, initGPReg64 r => ctx.regState r
| _, fnStartGPReg64 r => ctx.fnStartRegState r
| _, mcStack a w => (ctx.mcMemOps w).readMem ctx.memory (toSMT a)
| _, llvmVar nm tp => ctx.phiVarMap nm tp
| _, eq e1 e2 => SMT.eq (toSMT e1) (toSMT e2)
| _, bvAdd e1 e2 => SMT.bvadd (toSMT e1) (toSMT e2)
| _, bvSub e1 e2 => SMT.bvsub (toSMT e1) (toSMT e2)
| _, bvDecimal n width => SMT.bvimm width n

end BlockExpr



-- | Pretty print an error that occurs at the start of an instruction.
def renderMCInstError (fnm blockLbl : String) (idx : Nat) (addr : Nat) (msg : String) : String:= fnm++"."++blockLbl++"."++idx.repr++"("++addr.ppHex++"). "++msg

def standaloneGoalFilename (fnName blockLabel : String) (goalIndex : Nat) : String :=
fnName ++ "_" ++ blockLabel ++ "_" ++ goalIndex.repr ++ ".smt2"

/-- Write assert the negated goal and write out the resulting script
    of commands to a file. -/
def exportCheckSatProblem
(outputDir fnName blockLabel : String)
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
file ← IO.FS.Handle.mk (standaloneGoalFilename fnName blockLabel cnt) IO.FS.Mode.write;
-- TODO make these actual commands in our Lean4 SMT namespace
file.putStr ("; "++ goalName ++ "\n");
cmds.forM $ λ c => file.putStr $ (toString (toSExpr c)) ++ "\n"


def exportCallbacks
{α}
(outputDir fnName blockLabel : String)
(action : ProverInterface → IO α)
: IO α
:= do
goalCounter <- IO.mkRef 0;
let initSmtM : smtM Unit := pure ();
cmdRef <- IO.mkRef initSmtM;
action
  {addCommandCallback := λ cmd => cmdRef.modify (λ cmds => cmds *> liftCommand cmd),
   proveFalseCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef p msg,
   proveTrueCallback := λ p msg =>
    exportCheckSatProblem outputDir fnName blockLabel goalCounter cmdRef (SMT.not p) msg,
   blockErrorCallback := λ i a msg =>
    -- FIXME stderr and other handles are in Lean4, fix when we bump next
    IO.println $ "Error: " ++ renderMCInstError fnName blockLabel i a msg
  }


end ReoptVCG
