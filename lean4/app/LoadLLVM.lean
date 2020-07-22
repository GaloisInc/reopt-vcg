
import LeanLLVM.LLVMLib
import LeanLLVM.Load

namespace ReoptVCG

/-- Load the LLVM module in the given file. This function
    is pulled into its own module due to compilation time
    concerns (i.e., it's dependency on details of LLVMLib). --/
def loadLLVMModule (filePath : String) : IO LLVM.Module := do
ctx ← LLVM.FFI.newContext;
mb ← LLVM.FFI.newMemoryBufferFromFile filePath;
b ← LLVM.parseAssembly mb ctx "e-m:e-i64:64-f80:128-n8:16:32:64-S128";
match b with
| Except.ok m => LLVM.loadModule m
| Except.error msg => throw $ IO.userError $ "Failed to load LLVM module at `" ++ filePath ++ "`: " ++ msg

end ReoptVCG
