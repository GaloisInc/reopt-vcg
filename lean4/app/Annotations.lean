import Galois.Init.Json
import Init.Data.UInt
import Init.Lean.Data.Json
import Init.Lean.Data.Json.Basic
import Init.Lean.Data.Json.Printer
import Init.Lean.Data.Json.FromToJson
import Init.Data.RBMap
import Main.Elf


namespace ReoptVCG

open elf.elf_class (ELF64)
open Lean (Json HasFromJson HasToJson Array.hasFromJson List.hasToJson Nat.hasToJson Json.arr)
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

instance ModuleAnnotations.hasFromJson : HasFromJson ModuleAnnotations :=
⟨ModuleAnnotations.fromJson⟩
instance ModuleAnnotations.hasToJson : HasToJson ModuleAnnotations :=
⟨ModuleAnnotations.toJson⟩


------------------------------------------------------------------------
-- LocalIdent

/-- A local LLVM identifier --/
structure LocalIdent := (name : String)

def parseLocalIdent (js : Json) : Except String LocalIdent :=
match js.getStr? with
| Option.some s => pure $ LocalIdent.mk s
| _ => 
  match js.getNat? with
  | Option.some n => 
    if h : n < uint64Sz
    then pure $ LocalIdent.mk $ n.repr
    else Except.error $
         "Allocation name nonnegative integer must fit in a UInt64, but got" 
         ++ (Lean.Json.pretty js)
  | _ => 
    Except.error $ 
    "Allocation name expected a nonnegative integer or string, not "
    ++ (Lean.Json.pretty js)

def LocalIdent.fromJson (js : Json) : Option LocalIdent :=
(parseLocalIdent js).toOption

def LocalIdent.toJson (l : LocalIdent) : Json := toJson l.name

instance LocalIdent.hasFromJson : HasFromJson LocalIdent :=
⟨LocalIdent.fromJson⟩
instance LocalIdent.hasToJson : HasToJson LocalIdent :=
⟨LocalIdent.toJson⟩


------------------------------------------------------------------------
-- AllocaAnn

/-- Provides a mapping between LLVM alloca and machine code stack usage. --/
structure AllocaAnn :=
(ident : LocalIdent)
-- ^ The LLVM identifier initialized by the allocation.
(binOffset : Nat)
-- ^ Number of bytes from start of alloca to offset of stack
-- pointer in machine code.
--
-- The stack grows down, so the actual memory addresses represented
-- are
-- @[rsp0 - allocaBinaryOffset, rsp0 - allocaBinaryOffset + allocaSize)@
-- where @rsp0@ denotes the value of @rsp@ when the function starts.
(size : Nat)
-- ^ Size of allocation in bytes.
(existing : Bool)
-- ^ Stores true if the allocation already exists at this block.
-- The default is true, so we only need to assign this to false.

def parseAllocaAnn (js:Json) : Except String AllocaAnn := do
ident ← 
  match js.getObjVal? "llvm_ident" with
  | Option.some rawJs => parseLocalIdent rawJs
  | Option.none => throw $ "`llvm_ident` field was missing from annotation.";
off ← parseObjValAsNat js "offset";
sz ← parseObjValAsNat js "size";
ex ← parseObjValAsBoolD js "existing" true;
when (sz > off) $
  throw $ "Allocation size "
        ++sz.repr
        ++" must not be greater than offset "
        ++off.repr++".";
pure $ { ident := ident,
         binOffset := off,
         size := sz,
         existing := ex
       }


def AllocaAnn.fromJson (js : Json) : Option AllocaAnn :=
(parseAllocaAnn js).toOption

def AllocaAnn.toJson (ann : AllocaAnn) : Json := 
toJson $ RBMap.fromList [ ("llvm_ident", toJson ann.ident)
                        , ("offset", toJson ann.binOffset)
                        , ("size", toJson ann.size)
                        , ("existing", toJson ann.existing)
                        ]
                        Lean.strLt

instance AllocaAnn.hasFromJson : HasFromJson AllocaAnn :=
⟨AllocaAnn.fromJson⟩
instance AllocaAnn.hasToJson : HasToJson AllocaAnn :=
⟨AllocaAnn.toJson⟩


------------------------------------------------------------------------
-- MemoryAnn

-- | Annotation on memory address.
inductive MemoryAnn
| binaryOnlyAccess : MemoryAnn
-- ^ The instruction at the address updates the binary
-- stack, but does not affect LLVM memory.
| jointStackAccess : LocalIdent → MemoryAnn
-- ^ The instructions at the address access the LLVM allocation
-- associated with the given name.
| heapAccess : MemoryAnn
-- ^ There is an access to heap memory.


def parseMemoryAnn (js:Json) : Except String MemoryAnn :=
Except.error "TODO: implement parseMemoryAnn"


def renderMemoryAnn (ann:MemoryAnn) : List (String × Json) :=
[("TODO: implement renderMemoryAnn", toJson "TODO: implement renderMemoryAnn")]


------------------------------------------------------------------------
-- MCAddr

-- | This represents the address of code.
--
-- For non-position independent executables, it is an absolute address.
--
-- For position independent executables and libraries, it is relative
-- to the base address.
--
-- For object files, it is the offset into the .text section.
structure MCAddr := (addr : elf.word ELF64)


structure MCMemoryEvent :=
(addr : MCAddr)
-- ^ Address in machine code where event occurs.
(info : MemoryAnn)


def MCMemoryEvent.fromJson (js : Json) : Option MCMemoryEvent :=
Option.none -- TODO

def MCMemoryEvent.toJson (me : MCMemoryEvent) : Json := 
toJson $ "TODO: implement MCMemoryEvent.toJson" -- TODO

instance MCMemoryEvent.hasFromJson : HasFromJson MCMemoryEvent :=
⟨MCMemoryEvent.fromJson⟩
instance MCMemoryEvent.hasToJson : HasToJson MCMemoryEvent :=
⟨MCMemoryEvent.toJson⟩




structure ReachableBlockAnn :=
(startAddr : Nat) -- FIXME
 -- ^ Address of start of block in machine code
(codeSize : Nat) -- FIXME
 -- ^ Number of bytes in block
(x87Top : Nat) -- FIXME
 -- ^ The top of x87 stack (empty = 7, full = 0)
(dfFlag : Bool)
 -- ^ The value of the DF flag (default = False)
(preconds : List Nat) -- FIXME
 -- ^ List of preconditions for block.
(allocas : RBMap String AllocaAnn Lean.strLt)
-- ^ Maps identifiers to the allocation used to initialize them.
--
-- The same allocations should be used across the function, but
-- some block may not have been initialized.
(memoryEvents : List MCMemoryEvent)
-- ^ Annotates events within the block.


inductive BlockAnn
| reachable : ReachableBlockAnn → BlockAnn
| unreachable : BlockAnn


def parseBlockAnn (js:Json) : Except String BlockAnn :=
Except.error "TODO: implement parseBlockAnn"


def BlockAnn.toJson (block_label:String) : BlockAnn → Json
| BlockAnn.unreachable =>
  toJson $ RBMap.fromList [("label", toJson block_label),
                           ("reachable", toJson false)]
                        Lean.strLt
| BlockAnn.reachable ann =>
  toJson $ RBMap.fromList 
           [("label", toJson block_label),
            ("addr", toJson ann.startAddr),
            ("size", toJson ann.codeSize),
            ("x87_top", toJson ann.x87Top),
            ("df_flag", toJson ann.dfFlag),
            ("preconditions", arr (ann.preconds.map toJson).toArray),
            ("allocas", arr $ (ann.allocas.revFold (λ as _ a => (toJson a)::as) []).toArray),
            ("mem_events", arr $ (ann.memoryEvents.map toJson).toArray)
           ]
           Lean.strLt



end ReoptVCG
