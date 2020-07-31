

import ReoptVCG.Annotations
import ReoptVCG.SMTParser
import ReoptVCG.SMT
import SMTLIB.Syntax


namespace Test

namespace SMTExport

open ReoptVCG


def smtCommands1 : SMT.smtM Unit := do
tt ← SMT.declare_fun "tt" [] SMT.sort.smt_bool;
tt0 ← SMT.declare_fun "tt" [] SMT.sort.smt_bool;
tt2 ← SMT.name_term "tt2" SMT.true;
tt2_0 ← SMT.name_term "tt2_0" SMT.true;
tt2_1 ← SMT.name_term "tt2" SMT.true;
tt2_2 ← SMT.name_term "tt2" SMT.true;
tt2_0_0 ← SMT.name_term "tt2_0" SMT.true;
ff ← SMT.declare_fun "ff" [] SMT.sort.smt_bool;
negb ← SMT.declare_fun "negb" [SMT.sort.smt_bool] SMT.sort.smt_bool;
andb ← SMT.define_fun "andb" [SMT.sort.smt_bool, SMT.sort.smt_bool] SMT.sort.smt_bool (λ x y => SMT.and x y);
SMT.assert $ SMT.eq tt SMT.true;
SMT.assert $ SMT.eq tt tt2;
SMT.assert $ SMT.eq ff SMT.false;
SMT.assert $ SMT.eq (negb ff) SMT.true;
SMT.assert $ SMT.eq (negb tt) SMT.false;
SMT.assert $ andb tt (negb ff)

def proverAction1 (p : ProverInterface) : IO Unit := do
p.addSMTCallback smtCommands1;
p.proveFalseCallback SMT.false "false-is-false\n(true-is-true?)"

def testExportCallbacks : IO Unit := do
let outDir := ".";
let outFnNm := "foo";
let blockLbl := LLVM.BlockLabel.mk $ LLVM.Ident.named "bar";
exportCallbacks outDir outFnNm blockLbl proverAction1;
let outFile := outDir ++ [System.FilePath.pathSeparator].asString ++ (standaloneGoalFilename outFnNm blockLbl 0);
outFileContents ← IO.FS.readFile outFile;
IO.println outFileContents

def test : IO UInt32 := do
testExportCallbacks;
pure 0

end SMTExport

end Test
