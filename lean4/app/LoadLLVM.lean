
import LeanLLVM.LLVMLib

namespace ReoptVCG

/-- Load the LLVM module in the given file. This function
    is pulled into its own module due to compilation time
    concerns (i.e., it's dependency on details of LLVMLib). --/
def loadLLVMModule (filePath : String) : IO llvm.module := do
ctx ← llvm.ffi.newContext;
mb ← llvm.ffi.newMemoryBufferFromFile filePath;
b ← llvm.ffi.parseAssembly mb ctx;
llvm.loadModule b

end ReoptVCG
