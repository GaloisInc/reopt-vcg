import Galois.Data.RBMap
import Galois.Data.SExp
import Galois.Init.Json
import Galois.Init.Nat
import Init.Data.UInt
import Lean.Data.Json
import Lean.Data.Json.Basic
import Lean.Data.Json.Printer
import Lean.Data.Json.FromToJson
import Std.Data.RBMap
import LeanLLVM.AST
import ReoptVCG.Elf
import ReoptVCG.SmtParser
import SmtLib.Smt
import X86Semantics.Common

open Std (RBMap)

open Smt hiding Array

namespace LLVM
namespace ident
instance : ToString Ident := ⟨Ident.asString⟩
end ident
end LLVM

namespace ReoptVCG

open elf.elf_class (ELF64)
open Lean (Json FromJson ToJson Json.arr)
open Lean.FromJson (fromJson?)
open Lean.ToJson (toJson)
open Lean.Json
open WellFormedSExp

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

def MCAddr.decEq : ∀ (a b : MCAddr), Decidable (a = b)
| ⟨addr1⟩, ⟨addr2⟩ =>
  if h : addr1 = addr2
  then isTrue (h ▸ rfl)
  else isFalse (fun h' => MCAddr.noConfusion h' (fun h' => absurd h' h))

def MCAddr.toNat (a : MCAddr) : Nat := a.addr.toNat

instance MCAddr.hasDecidableEq : DecidableEq MCAddr := MCAddr.decEq


def parseMCAddr (js : Json) : Except String MCAddr := do
match js.getStr? with
| Option.some addrStr => match Nat.fromHexString addrStr with
  | Option.some n => match elf.word.fromNat ELF64 n with
    | Option.some w => pure $ MCAddr.mk w
    | Option.none =>
      throw $ "Expected the hexadecimal number to be a valid machine code address, but got: " ++ js.pretty
  | Option.none =>
    throw $ "Expected the string to contain a hexadecimal machine code address, but got: " ++ js.pretty
| Option.none => match js.getNat? with
  | Option.some n => match elf.word.fromNat ELF64 n with
    | Option.some w => pure $ MCAddr.mk w
    | Option.none =>
      throw $ "Expected the natural number to be a valid machine code address, but got: " ++ js.pretty
  | Option.none =>
    throw $ "Expected a string or natural number for the machine code address, but got: " ++ js.pretty

def MCAddr.fromJson? (js:Json) : Option MCAddr :=
  (parseMCAddr js).toOption

protected
def MCAddr.toJson (m:MCAddr) : Json :=
  toJson $ Nat.ppHex $ UInt64.toNat m.addr

instance MCAddr.hasFromJson : FromJson MCAddr :=
  ⟨MCAddr.fromJson?⟩
instance MCAddr.hasToJson : ToJson MCAddr :=
  ⟨MCAddr.toJson⟩

def parseObjValAsMCAddr (js:Json) (key:String) : Except String MCAddr :=
  match js.getObjVal? key with
  | Option.some o => parseMCAddr o
  | Option.none => throw $ "Missing a `" ++ key ++ "` entry"

------------------------------------------------------------------------
-- FucntionAnn

structure FunctionAnn :=
(llvmFnName : String)
-- ^ LLVM function name
(startAddr  : MCAddr) 
-- ^ Address of start of block in machine code.  Here so we don't
-- rely on the order of blocks.  This needs to be checked.
(blocks : Array Json)
-- ^ Maps LLVM labels to an JSON object describing information associated with
-- that block.

-- Like FunctionAnn.fromJson but with human-friendly error messages.
def parseFunctionAnn (js:Json) : Except String FunctionAnn := do
  let name ←  parseObjValAsString js "llvm_name"
  let startAddr ←  parseObjValAsMCAddr js "start_addr"
  let blocks ← parseObjValAsArr js "blocks"
  pure $ FunctionAnn.mk name startAddr blocks

protected
def FunctionAnn.fromJson? (js : Json) : Option FunctionAnn := (parseFunctionAnn js).toOption

protected
def FunctionAnn.toJson (fnAnn : FunctionAnn) : Json :=
  toJson $ Std.RBMap.fromList [ ("llvm_name", toJson fnAnn.llvmFnName)
                              , ("start_addr", toJson fnAnn.startAddr)
                              , ("blocks", toJson fnAnn.blocks)]
                              Lean.strLt

instance FunctionAnn.hasFromJson : FromJson FunctionAnn := ⟨FunctionAnn.fromJson?⟩
instance FunctionAnn.hasToJson : ToJson FunctionAnn := ⟨FunctionAnn.toJson⟩

-- External functions (i.e. axiomatic)

structure ExternalFunctionAnn :=
(llvmFnName : String)
(startAddr  : MCAddr) 
 -- ^ Address of start of block in machine code
(isNoReturn : Bool)

-- Like FunctionAnn.fromJson but with human-friendly error messages.
def parseExternalFunctionAnn (js:Json) : Except String ExternalFunctionAnn := do
  let name ←  parseObjValAsString js "llvm_name"
  let startAddr ← parseObjValAsMCAddr js "start_addr"
  let isNoReturn <- parseObjValAsBool js "is_no_return"
  pure $ ExternalFunctionAnn.mk name startAddr isNoReturn

protected
def ExternalFunctionAnn.fromJson? (js : Json) : Option ExternalFunctionAnn := (parseExternalFunctionAnn js).toOption

protected
def ExternalFunctionAnn.toJson (fnAnn : ExternalFunctionAnn) : Json :=
    toJson $ Std.RBMap.fromList [ ("llvm_name", toJson fnAnn.llvmFnName)
                              , ("start_addr", toJson fnAnn.startAddr)
                              , ("is_no_return", toJson fnAnn.isNoReturn)]
                              Lean.strLt

instance ExternalFunctionAnn.hasFromJson : FromJson ExternalFunctionAnn := ⟨ExternalFunctionAnn.fromJson?⟩
instance ExternalFunctionAnn.hasToJson : ToJson ExternalFunctionAnn := ⟨ExternalFunctionAnn.toJson⟩


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
(extFunctions : List ExternalFunctionAnn)

def ModuleAnnotations.defaultPageSize : Nat := 4096

-- Like ModuleAnnotaions.fromJson but with human-friendly error messages.
def parseAnnotations (js:Json) : Except String ModuleAnnotations := do
  let llvmFile ← parseObjValAsString js "llvm_path"
  let binFile ← parseObjValAsString js "binary_path"
  let pgSize ← parseObjValAsNatD js "page_size" ModuleAnnotations.defaultPageSize
  if Nat.land pgSize (pgSize - 1) > 0 then
    throw $ "`page_size` value must be a power of 2, but got `"++pgSize.repr++"`."
  let guardCount ← parseObjValAsNat js "stack_guard_pages";
  if guardCount == 0 then
    throw "There must be at least one guard page."
  let fnsArr ← parseObjValAsArrWith parseFunctionAnn js "functions"
  let extFnsArr ← parseObjValAsArrWith parseExternalFunctionAnn js "extfunctions"

  pure $ { llvmFilePath := llvmFile,
           binFilePath := binFile,
           pageSize := pgSize,
           stackGuardPageCount := guardCount,
           functions := fnsArr.toList,
           extFunctions := extFnsArr.toList
         }


def ModuleAnnotations.fromJson? (js : Json) : Option ModuleAnnotations :=
(parseAnnotations js).toOption

protected
def ModuleAnnotations.toJson (ann : ModuleAnnotations) : Json :=
toJson $ Std.RBMap.fromList [ ("llvm_path", toJson ann.llvmFilePath)
                            , ("binary_path", toJson ann.binFilePath)
                            , ("page_size", toJson ann.pageSize)
                            , ("stack_guard_pages", toJson ann.stackGuardPageCount)
                            , ("functions", toJson ann.functions.toArray)
                            , ("extfunctions", toJson ann.extFunctions.toArray)
                            ]
                        Lean.strLt

instance ModuleAnnotations.hasFromJson : FromJson ModuleAnnotations :=
  ⟨ModuleAnnotations.fromJson?⟩
instance ModuleAnnotations.hasToJson : ToJson ModuleAnnotations :=
  ⟨ModuleAnnotations.toJson⟩


------------------------------------------------------------------------
-- LocalIdent

/- A local LLVM identifier -/
structure LocalIdent := (name : String)

namespace LocalIdent

def lt : forall (x y : LocalIdent), Prop
  | { name := x }, {name := y } => x < y

instance : HasLess LocalIdent := ⟨lt⟩

instance decLt : ∀(x y:LocalIdent), Decidable (x < y)
| { name := x }, { name := y } =>
  (match String.decLt x y with
   | Decidable.isTrue  p => Decidable.isTrue p
   | Decidable.isFalse p => Decidable.isFalse p
   )

end LocalIdent

def parseLocalIdent (js : Json) : Except String LocalIdent :=
match js.getStr? with
| Option.some s => pure $ LocalIdent.mk s
| _ => 
  match js.getNat? with
  | Option.some n => 
    if h : n < UInt64.size 
    then pure $ LocalIdent.mk $ n.repr
    else Except.error $
         "Allocation name nonnegative integer must fit in a UInt64, but got" 
         ++ (Lean.Json.pretty js)
  | _ => 
    Except.error $ 
    "Allocation name expected a nonnegative integer or string, not "
    ++ (Lean.Json.pretty js)

def LocalIdent.fromJson? (js : Json) : Option LocalIdent :=
  (parseLocalIdent js).toOption

protected
def LocalIdent.toJson (l : LocalIdent) : Json := toJson l.name

instance LocalIdent.hasFromJson : FromJson LocalIdent :=
  ⟨LocalIdent.fromJson?⟩
instance LocalIdent.hasToJson : ToJson LocalIdent :=
  ⟨LocalIdent.toJson⟩


------------------------------------------------------------------------
-- AllocaAnn

/- Provides a mapping between LLVM alloca and machine code stack usage. -/
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
  let ident ← 
    match js.getObjVal? "llvm_ident" with
    | Option.some rawJson => parseLocalIdent rawJson
    | Option.none => throw $ "`llvm_ident` field was missing from annotation.";
  let off ← parseObjValAsNat js "offset";
  let sz ← parseObjValAsNat js "size";
  let ex ← parseObjValAsBoolD js "existing" true;
  if sz > off then
    throw $ "Allocation size "
          ++sz.repr
          ++" must not be greater than offset "
          ++off.repr++".";
  pure $ { ident := ident,
           binOffset := off,
           size := sz,
           existing := ex
         }


def AllocaAnn.fromJson? (js : Json) : Option AllocaAnn :=
  (parseAllocaAnn js).toOption

protected
def AllocaAnn.toJson (ann : AllocaAnn) : Json := 
  toJson $ Std.RBMap.fromList [ ("llvm_ident", toJson ann.ident)
                              , ("offset", toJson ann.binOffset)
                              , ("size", toJson ann.size)
                              , ("existing", toJson ann.existing)
                              ]
                              Lean.strLt

instance AllocaAnn.hasFromJson : FromJson AllocaAnn :=
  ⟨AllocaAnn.fromJson?⟩
instance AllocaAnn.hasToJson : ToJson AllocaAnn :=
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


def parseMemoryAnn (js:Json) : Except String MemoryAnn := do
  let tp ← parseObjValAsString js "type"
  match tp with
  | "binary_only_access" => pure MemoryAnn.binaryOnlyAccess
  | "joint_stack_access" => match js.getObjVal? "alloca" with
    | Option.some rawAllocaJson => do
      let lIdent ← parseLocalIdent rawAllocaJson
      pure $ MemoryAnn.jointStackAccess lIdent
    | Option.none =>
      throw $ "Expected a local ident in the `alloca` field of a `joint_stack_access` memory annotation"
  | "heap_access" => pure MemoryAnn.heapAccess
  | _ => throw $ "Unexpected memory annotation type type: " ++ js.pretty


def renderMemoryAnn : MemoryAnn → List (String × Json)
| MemoryAnn.binaryOnlyAccess =>
  [("type", toJson "binary_only_access")]
| MemoryAnn.jointStackAccess x =>
  [("type", toJson "joint_stack_access"),
   ("alloca", toJson x)]
| MemoryAnn.heapAccess =>
  [("type", toJson "heap_access")]



structure MCMemoryEvent :=
(addr : MCAddr)
-- ^ Address in machine code where event occurs.
(info : MemoryAnn)


def parseMCMemoryEvent (js : Json) : Except String MCMemoryEvent := do
  let addr ← parseObjValAsMCAddr js "addr"
  let info ← parseMemoryAnn js
  pure $ MCMemoryEvent.mk addr info



def MCMemoryEvent.fromJson? (js : Json) : Option MCMemoryEvent :=
  (parseMCMemoryEvent js).toOption

protected
def MCMemoryEvent.toJson (me : MCMemoryEvent) : Json := 
  let entries : List (String × Json) :=
    [ ("addr", toJson me.addr)] ++ (renderMemoryAnn me.info)
  toJson $ Std.RBMap.fromList entries Lean.strLt


instance MCMemoryEvent.hasFromJson : FromJson MCMemoryEvent :=
  ⟨MCMemoryEvent.fromJson?⟩

instance MCMemoryEvent.hasToJson : ToJson MCMemoryEvent :=
  ⟨MCMemoryEvent.toJson⟩

------------------------------------------------------------------------
-- BlockVar

/- Callee saved registers. -/
def x86CalleeSavedGPRegs : List x86.reg64 :=
[ x86.reg64.rbp,
  x86.reg64.rbx,
  x86.reg64.r12,
  x86.reg64.r13,
  x86.reg64.r14,
  x86.reg64.r15 ]

/- General purpose registers that may be used to pass arguments. -/
def x86ArgGPRegs : List x86.reg64 :=
[ x86.reg64.rdi,
  x86.reg64.rsi,
  x86.reg64.rdx,
  x86.reg64.rcx,
  x86.reg64.r8,
  x86.reg64.r9 ]

/- General purpose registers that may be used to pass arguments. -/
def x86ResultGPRegs : List x86.reg64 :=
[ x86.reg64.rax,
  x86.reg64.rdx
]

section
open mc_semantics (type)
open mc_semantics.type
open x86.avxreg_type
open x86.concrete_reg

def x86ArgFPRegs : List (x86.concrete_reg (bv 512)) :=
 [ avxreg (Fin.ofNat 0) zmm
 , avxreg (Fin.ofNat 1) zmm
 , avxreg (Fin.ofNat 2) zmm
 , avxreg (Fin.ofNat 3) zmm
 , avxreg (Fin.ofNat 4) zmm
 , avxreg (Fin.ofNat 5) zmm
 , avxreg (Fin.ofNat 6) zmm
 , avxreg (Fin.ofNat 7) zmm
 ]

def x86ResultFPRegs : List (x86.concrete_reg (bv 512)) :=
 [ avxreg (Fin.ofNat 0) zmm
 , avxreg (Fin.ofNat 1) zmm
 ]

end

def parsePrecondition (llvmMap: LLVMTyEnv) (js:Json) : Except String (BlockExpr SmtSort.bool) := do
  let rawStr ← match js.getStr? with
               | none => Except.error $ "Expected precondition to be a string but got: " ++ js.pretty ++ "."
               | some s => Except.ok s;
  BlockExpr.parseAs SmtSort.bool llvmMap rawStr


def blockExprToJson : ∀{tp:SmtSort}, BlockExpr tp → Json :=
  λ _ => toJson "TODO: implement exprToJson"

instance BlockExprHasToJson {tp:SmtSort} : ToJson (BlockExpr tp) :=
  ⟨blockExprToJson⟩

abbrev AllocaAnnMap : Type := RBMap LocalIdent AllocaAnn (λ x y => x<y)

structure ReachableBlockAnn :=
(startAddr : MCAddr) -- FIXME
 -- ^ Address of start of block in machine code
(codeSize : Nat) -- FIXME
 -- ^ Number of bytes in block
(x87Top : Nat) -- FIXME
 -- ^ The top of x87 stack (empty = 7, full = 0)
(dfFlag : Bool)
 -- ^ The value of the DF flag (default = false)
(preconds : Array (BlockExpr SmtSort.bool))
 -- ^ List of preconditions for block.
(allocas : AllocaAnnMap)
-- ^ Maps identifiers to the allocation used to initialize them.
--
-- The same allocations should be used across the function, but
-- some block may not have been initialized.
(memoryEvents : Array MCMemoryEvent)
-- ^ Annotates events within the block.
(isTailCall : Bool)
-- ^ If this block ends in a tail call (some false), and if that tail call is a
-- noreturn (some true). 


namespace ReachableBlockAnn

-- Default values for various ReachableBlockAnn optional entries.
def x87TopDefault : Nat := 7
def dfFlagDefault : Bool := false
def precondsDefault : Array (BlockExpr SmtSort.bool) := Array.empty
def allocasArrayDefault : Array AllocaAnn := Array.empty
def memoryEventsDefault : Array MCMemoryEvent := Array.empty

end ReachableBlockAnn

inductive BlockAnn
| reachable : ReachableBlockAnn → BlockAnn
| unreachable : BlockAnn


def parseReachableBlockAnn (llvmMap: LLVMTyEnv) (js:Json) : Except String ReachableBlockAnn := do
  let addr ← parseObjValAsMCAddr js "addr"
  let addrNat := addr.addr.toNat
  let size ← parseObjValAsNat js "size"
  if addrNat + size < addrNat then
    throw "Expected end of block computation to not overflow."
  let x87Top ← parseObjValAsNatD js "x87_top" ReachableBlockAnn.x87TopDefault
  let dfFlag ← parseObjValAsBoolD js "df_flag" ReachableBlockAnn.dfFlagDefault
  let preconds ← parseObjValAsArrWithD (parsePrecondition llvmMap) js "preconditions" ReachableBlockAnn.precondsDefault
  let allocas ← parseObjValAsArrWithD parseAllocaAnn js "allocas" ReachableBlockAnn.allocasArrayDefault
  let allocaMap := Std.RBMap.fromList (allocas.toList.map (λ a => (a.ident, a))) (λ x y => x<y)
  let memoryEvents ← parseObjValAsArrWithD parseMCMemoryEvent js "mem_events" ReachableBlockAnn.memoryEventsDefault
  let isTailCall <- parseObjValAsBool js "is_tail_call"

    -- match js.getObjVal? "tailCallStatus" with
    -- | Option.some rawJson => 
    --   match fromJson? rawJson with 
    --   | Option.none   => Except.error "Expected a boolean value"
    --   | Option.some b => pure (some b)
    -- | Option.none => pure none

  pure $ {startAddr := addr,
          codeSize := size,
          x87Top := x87Top,
          dfFlag := dfFlag,
          preconds := preconds,
          allocas := allocaMap,
          memoryEvents := memoryEvents,
          isTailCall   := isTailCall
         }

def parseBlockAnn (llvmMap: LLVMTyEnv) (js:Json) : Except String BlockAnn := do
  let isReachable ← parseObjValAsBoolD js "reachable" true
  if isReachable
  then BlockAnn.reachable <$> parseReachableBlockAnn llvmMap js
  else pure BlockAnn.unreachable

protected
def BlockAnn.toJson (block_label:String) : BlockAnn → Json
| BlockAnn.unreachable =>
  toJson $ Std.RBMap.fromList [("label", toJson block_label),
                              ("reachable", toJson false)]
                              Lean.strLt
| BlockAnn.reachable ann =>
  toJson $ Std.RBMap.fromList 
           [("label", toJson block_label),
            ("addr", toJson ann.startAddr),
            ("size", toJson ann.codeSize),
            ("x87_top", toJson ann.x87Top),
            ("df_flag", toJson ann.dfFlag),
            ("preconditions", arr (ann.preconds.map toJson)),
            ("allocas", arr $ (ann.allocas.revFold (λ as _ a => (toJson a)::as) []).toArray),
            ("mem_events", arr $ (ann.memoryEvents.map toJson)),
            ("is_tail_call", toJson ann.isTailCall)
           ]
           Lean.strLt


end ReoptVCG
