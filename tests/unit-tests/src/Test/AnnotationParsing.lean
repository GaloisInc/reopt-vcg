
import ReoptVCG.Annotations
import ReoptVCG.SmtParser
import Lean.Data.Json
import Lean.Data.Json.FromToJson
import Galois.Init.Json

namespace Test

namespace AnnotationParsing

open ReoptVCG

open Smt (SmtSort SmtSort.bv64)

-- Parse the ModuelAnnotations for the fib test example, printing any mismatches in expected field values,
-- and return the underlying FunctionAnn
def parseAnnotationsFibTest : IO FunctionAnn := do
  let homeDir ← (do
    let maybeVal ← IO.getEnv "REOPTVCGHOME";
    pure $ maybeVal.getD (panic "REOPTVCGHOME environment variable not set"));
  let fileContents ← IO.FS.readFile $ homeDir ++ "/test-programs/test_fib_diet_reopt.ann";
  match Lean.Json.parse fileContents with
  | Except.error errMsg => throw $ IO.userError $ "Failed to parse json string: " ++ errMsg
  | Except.ok js =>
    match parseAnnotations js with
    | Except.error errMsg => throw $ IO.userError $ "Failed to parse json as a module annotation: " ++ errMsg
    | Except.ok modAnn => do
      unless (modAnn.llvmFilePath == "test_fib_diet_reopt.ll") do
        throw $ IO.userError $ "Expected llvmFilePath `test_fib_diet_reopt.ll` but got: " ++ modAnn.llvmFilePath;
      unless (modAnn.binFilePath == "test_fib_diet_lld.exe") do
        throw $ IO.userError $ "Expected llvmFilePath `test_fib_diet_lld.exe` but got: " ++ modAnn.binFilePath;
      unless (modAnn.pageSize == 4096) do
        throw $ IO.userError $ "Expected pageSize `4096` but got: " ++ modAnn.pageSize.repr;
      unless (modAnn.stackGuardPageCount == 1) do
        throw $ IO.userError $ "Expected stackGuardPageCount `1` but got: " ++ modAnn.stackGuardPageCount.repr;
      match modAnn.functions with
      | [fibFn, mainFn] => do
        unless (fibFn.llvmFnName == "fib") do
          throw $ IO.userError $ "Expected first function annotation to be for `fib` but got: " ++ fibFn.llvmFnName;
        unless (mainFn.llvmFnName == "main") do
          throw $ IO.userError $ "Expected second function annotation to be for `main` but got: " ++ mainFn.llvmFnName;
        IO.println "parseAnnotationsFibTest done";
        pure fibFn
      | _ => throw $ IO.userError $ "Expected two function annotations but found " ++ modAnn.functions.length.repr


def fibLLVMTyEnvEntries : List (LLVM.Ident × SmtSort) :=
  ["t1", "t4", "t5", "t8", "t9", "t12", "t13", "t15"].map (λ nm => (LLVM.Ident.named nm, SmtSort.bv64))

def fibLLVMTyEnv : Std.RBMap LLVM.Ident SmtSort (λ x y => x<y) :=
  Std.RBMap.fromList fibLLVMTyEnvEntries (λ x y => x<y)

-- Parse and check a few very basic structural properties about the return block annotations
-- just to sanity check how things are working at the moment.
def parseBlockAnnFibTest (fibAnn : FunctionAnn) : IO Unit := do
  unless (fibAnn.llvmFnName == "fib") do
    throw $ IO.userError $ "Expected function annotation to be for `fib` but got: " ++ fibAnn.llvmFnName;
  match fibAnn.blocks.toList with
  | [bAnnJson, _block2, _block3, _block4, _block5, _block6] => do
    match parseBlockAnn fibLLVMTyEnv bAnnJson with
    | Except.error errMsg => do
      throw $ IO.userError $ "parseBlockAnn failed: " ++ errMsg
    | Except.ok BlockAnn.unreachable => do
      throw $ IO.userError $ "Unexpected unreachable block in fib!"
    | Except.ok (BlockAnn.reachable rbAnn) => do
      unless (rbAnn.startAddr.addr.toNat == 2101248) do
        throw $ IO.userError $ "Expected start address of 2101248 but got: " ++ rbAnn.startAddr.addr.toNat.repr;
      unless (rbAnn.codeSize == 23) do
        throw $ IO.userError $ "Expected code size of 23 but got: " ++ rbAnn.codeSize.repr;
      unless (rbAnn.x87Top == ReachableBlockAnn.x87TopDefault) do
        throw $ IO.userError $ "Expected x87Top "++ReachableBlockAnn.x87TopDefault.repr
                               ++ " but got: " ++ rbAnn.x87Top.repr;
      unless (rbAnn.preconds.size == 7) do
        throw $ IO.userError $ "Expected 7 preconditions but found: " ++ rbAnn.preconds.size.repr;
      unless (rbAnn.allocas.size == 0) do
        throw $ IO.userError $ "Expected no allocas but found: " ++ rbAnn.allocas.size.repr;
      unless (rbAnn.memoryEvents.size == 3) do
        throw $ IO.userError $ "Expected 3 memory events  but found: " ++ rbAnn.memoryEvents.size.repr;
      IO.println "parseBlockAnnFibTest done"
  | _ =>
    throw $ IO.userError $ "Expected annotation for `fib` to have 6 blocks but it had: " ++ fibAnn.blocks.size.repr;

  pure ()


def test : IO UInt32 := do
  let fAnn ← parseAnnotationsFibTest;
  parseBlockAnnFibTest fAnn;
  pure 0

end AnnotationParsing
end Test


