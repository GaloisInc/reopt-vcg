import LeanLLVM.LLVMLib
import LeanLLVM.Load

namespace Test

namespace LoadLLVM

def loadAsmFile (filePath : String) : IO (Except String LLVM.FFI.Module) := do
ctx ← LLVM.FFI.newContext;
mb ← LLVM.FFI.newMemoryBufferFromFile filePath;
LLVM.parseAssembly mb ctx "e-m:e-i64:64-f80:128-n8:16:32:64-S128"

def loadBitcodeFile (filePath : String) : IO (Except String LLVM.FFI.Module) := do
ctx ← LLVM.FFI.newContext;
mb ← LLVM.FFI.newMemoryBufferFromFile filePath;
LLVM.parseBitcodeFile mb ctx

def checkLoadPassed (action : IO (Except String LLVM.FFI.Module)) : IO Unit := do
res <- action;
match res with
| Except.ok m => do
  _ <- LLVM.loadModule m;
  IO.println "pass"
| Except.error msg => do
  IO.print "fail: ";
  IO.println msg

def checkLoadFailed (action : IO (Except String LLVM.FFI.Module)) : IO Unit := do
res <- action;
match res with
| Except.ok m => do
  _ <- LLVM.loadModule m;
  IO.println "fail"
| Except.error msg => do
  IO.println "pass"


def test : IO UInt32 := do
checkLoadPassed (loadAsmFile "llvm_asm_example.ll");
checkLoadFailed (loadAsmFile "llvm_bitcode_example.bc");
checkLoadPassed (loadBitcodeFile "llvm_bitcode_example.bc");
checkLoadFailed (loadBitcodeFile "llvm_asm_example.ll");
pure 0


end LoadLLVM
end Test
