
import LeanLLVM.LLVMLib

namespace ReoptVCG

/- Load the LLVM module in the given file. This function
   is pulled into its own module due to compilation time
   concerns (i.e., it's dependency on details of LLVMLib). -/
def loadLLVMModule (filePath : System.FilePath) : IO LLVM.Module := do
let ctx ← LLVM.FFI.newContext
let mb ← LLVM.FFI.newMemoryBufferFromFile filePath.toString
let b ← LLVM.FFI.parseAssembly mb ctx
LLVM.loadModule b

end ReoptVCG
