
import Init.Lean.Data.Json
import Init.Lean.Data.Json.Printer
import Galois.Init.Json
import Init.Data.RBMap



namespace ReoptVCG


open Lean (Json HasFromJson HasToJson)
open Lean.Json

structure FunctionAnn :=
(llvmFunName : String)
-- ^ LLVM function name
(blocks : Array Json)
-- ^ Maps LLVM labels to an JSON object describing information associated with
-- that block.

-- Like FunctionAnn.fromJson but with human-friendly error messages.
def parseFunctionAnn (js:Json) : Except String FunctionAnn := do
name ←  parseObjValAsString js "llvm_name";
blocks ← parseObjValAsArr js "blocks";
pure $ FunctionAnn.mk name blocks


def FunctionAnn.fromJson (js : Json) : Option FunctionAnn := (parseFunctionAnn js).toOption

def FunctionAnn.toJson (fnAnn : FunctionAnn) : Json :=
toJson $ RBMap.fromList [ ("llvm_name", toJson fnAnn.llvmFunName)
                        , ("blocks", toJson fnAnn.blocks)]
                        Lean.strLt

instance FunctionAnn.hasFromJson : HasFromJson FunctionAnn := ⟨FunctionAnn.fromJson⟩
instance FunctionAnn.hasToJson : HasToJson FunctionAnn := ⟨FunctionAnn.toJson⟩



structure ModuleAnnotations :=
(llvmFilePath : String)
  -- ^ Path to LLVM .bc or .ll file path
(binFilePath :  String)
  -- ^ Binary file path that will be analyzed by Macaw.
(pageSize : Nat)
  -- ^ The number of bytes in a page (must be a power of 2)
(stackGuardPageCount : Nat)
  -- ^ The number of unallocated pages beneath the stack.
(functions : List FunctionAnn)

def ModuleAnnotations.defaultPageSize : Nat := 4096

-- Like ModuleAnnotaions.fromJson but with human-friendly error messages.
def parseAnnotations (js:Json) : Except String ModuleAnnotations := do
llvmFile ← parseObjValAsString js "llvm_path";
binFile ← parseObjValAsString js "binary_path";
pgSize ← parseObjValAsNatD js "page_size" ModuleAnnotations.defaultPageSize;
when (Nat.land pgSize (pgSize - 1) > 0) $
  throw $ "`page_size` value must be a power of 2, but got `"++pgSize.repr++"`.";
guardCount ← parseObjValAsNat js "stack_guard_pages";
when (guardCount == 0) $
  throw "There must be at least one guard page.";
fnsArr ← parseObjValAsArrWith parseFunctionAnn js "functions";
pure $ { llvmFilePath := llvmFile,
         binFilePath := binFile,
         pageSize := pgSize,
         stackGuardPageCount := guardCount,
         functions := fnsArr.toList
       }


def ModuleAnnotations.fromJson (js : Json) : Option ModuleAnnotations :=
(parseAnnotations js).toOption

def ModuleAnnotations.toJson (ann : ModuleAnnotations) : Json :=
toJson $ RBMap.fromList [ ("llvm_path", toJson ann.llvmFilePath)
                        , ("binary_path", toJson ann.binFilePath)
                        , ("page_size", toJson ann.pageSize)
                        , ("stack_guard_pages", toJson ann.stackGuardPageCount)
                        , ("functions", toJson ann.functions.toArray)
                        ]
                        Lean.strLt


end ReoptVCG
