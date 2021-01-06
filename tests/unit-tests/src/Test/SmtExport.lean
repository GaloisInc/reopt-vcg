

import ReoptVCG.Annotations
import ReoptVCG.SmtParser
import ReoptVCG.Smt
import SmtLib.Smt


namespace Test

namespace SmtExport

open ReoptVCG
open Smt


def smtGoal1 : Smt.SmtM (Smt.Term SmtSort.bool) := do
  let tt ← Smt.declareFun "tt" [] SmtSort.bool;
  let tt0 ← Smt.declareFun "tt" [] SmtSort.bool;
  let tt2 ← Smt.nameTerm "tt2" Smt.true;
  let tt2_0 ← Smt.nameTerm "tt2_0" Smt.true;
  let tt2_1 ← Smt.nameTerm "tt2" Smt.true;
  let tt2_2 ← Smt.nameTerm "tt2" Smt.true;
  let tt2_0_0 ← Smt.nameTerm "tt2_0" Smt.true;
  let ff ← Smt.declareFun "ff" [] SmtSort.bool;
  let negb ← Smt.declareFun "negb" [SmtSort.bool] SmtSort.bool;
  let andb ← Smt.defineFun "andb" [SmtSort.bool, SmtSort.bool] SmtSort.bool (λ x y => Smt.and x y);
  Smt.assert $ Smt.eq tt Smt.true;
  Smt.assert $ Smt.eq tt tt2;
  Smt.assert $ Smt.eq ff Smt.false;
  Smt.assert $ Smt.eq (negb ff) Smt.true;
  Smt.assert $ Smt.eq (negb tt) Smt.false;
  Smt.assert $ andb tt (negb ff);
  pure Smt.true

def testExportCallbacks : IO Unit := do
  let outDir := ".";
  let outFnNm := "foo";
  let blockLbl := LLVM.BlockLabel.mk $ LLVM.Ident.named "bar";
  let vg : VerificationGoal :=
    {loc := {fnName := outFnNm,
             blockLbl := blockLbl,
             llvmInstrIdx := 0,
             mcAddr := 0},
     index := 0,
     tag := GoalTag.blockPrecondition,
     extraInfo := "false-is-false\n(true-is-true?)",
     goal := smtGoal1};
  let ps ← exportProverSession outDir;
  ps.verifyGoal {annFile := "", semanticsBackend := SemanticsBackend.ManualSemantics, mode := VerificationMode.defaultMode, verbose := false} vg;
  discard $ ps.sessionComplete;
  let outFile := outDir ++ [System.FilePath.pathSeparator].asString ++ (standaloneGoalFilename vg);
  let outFileContents ← IO.FS.readFile outFile;
  IO.println ""
  IO.println "Exported file contents:"
  IO.println outFileContents

def test : IO UInt32 := do
  testExportCallbacks;
  pure 0

end SmtExport

end Test
