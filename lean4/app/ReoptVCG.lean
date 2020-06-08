import Galois.Init.Json
import LeanLLVM.AST
import Main.Elf
import ReoptVCG.Annotations
import ReoptVCG.LoadLLVM
import ReoptVCG.Types
import SMTLIB.Syntax
import X86Semantics.Common

namespace ReoptVCG

open Lean (Json strLt)
open Lean.Json (parseObjValAsString)

open elf.elf_class (ELF64)
open llvm (llvm_type llvm_type.prim_type llvm_type.ptr_to prim_type prim_type.integer)

def exportModeCallbacks {α : Type} (outDir : String) (fn : FnName) (lbl : llvm.block_label) (action : ProverInterface → IO α) : IO α :=
-- FIXME
action $ ProverInterface.mk (λ _ => pure ()) (λ _ _ => pure ()) (λ _ _ => pure ()) (λ _ _ _ => pure ())


-- This runs an action with a proof session generator, and reports
-- the final proof results.
def interactiveSMTGenerator (annPath solverPath : String) (solverArgs : List String) : IO ProverSessionGenerator :=
-- FIXME
pure $ ProverSessionGenerator.mk (λ _ _ _ => pure ()) (pure ())


/-- Lift an Except to IO, throwing any occurring error with the given prefix at the front of the message. --/
def elseThrowPrefixed {ε α : Type} [HasToString ε] (e : Except ε α) (pfx : String) : IO α :=
match e with
| Except.ok a    => pure a
| Except.error e => throw (IO.userError $ pfx ++ (toString e))

-- | Use a map from symbol names to address to find address.
def getMCAddrOfLLVMFunction
(m : RBMap String (elf.word ELF64) Lean.strLt)
-- ^ Map from symbol names in machine code
-- to the address in the binary.
(fnm : String)
-- ^ Function name
: Except String MCAddr := do
match m.find? fnm with
| Option.none => throw $ "Cannot find address of LLVM symbol: " ++ fnm
| Option.some expectedAddr => pure $ MCAddr.mk expectedAddr


/-- Callee saved registers. --/
def x86CalleeSavedGPRegs : List x86.Reg64 :=
[ x86.Reg64.rbp,
  x86.Reg64.rbx,
  x86.Reg64.r12,
  x86.Reg64.r13,
  x86.Reg64.r14,
  x86.Reg64.r15 ]

/-- General purpose registers that may be used to pass arguments. --/
def x86ArgGPRegs : List x86.Reg64 :=
[ x86.Reg64.rdi,
  x86.Reg64.rsi,
  x86.Reg64.rdx,
  x86.Reg64.rcx,
  x86.Reg64.r8,
  x86.Reg64.r9 ]


def llvmTypeToSort : llvm_type → Option SMTLIB.sort
| llvm_type.prim_type (prim_type.integer lw) =>
  Option.some $ SMTLIB.sort.bitvec lw
| llvm_type.ptr_to _ => Option.none
| _ => Option.none


/-- Maps between LLVM argument and machine code name. --/
structure LLVMMCArgBinding :=
(llvmArgName : llvm.ident)
(smtSort: SMTLIB.sort)
(register: x86.Reg64)



/-- Verify a block satisfies its specification. --/
def verifyBlock
(funAnn : FunctionAnn)
 -- ^ Annotations for function
(argBindings : List LLVMMCArgBinding)
(blockMap : ReachableBlockAnnMap)
-- ^ Annotations on blocks.
(firstLabel : llvm.block_label)
 -- ^ Label of first block.
(bAnn : AnnotatedBlock)
: ModuleVCG Unit := do
moduleThrow "TODO: implement verifyBlock"



/-- Extract the phi statements from the list of statements, returning
    either the name of the variable and type that could not be interpreted
    or a map from from variable names to their types. --/
def extractPhiStmtVars : 
List (llvm.ident × llvm_type × BlockLabelValMap) →
List llvm.stmt →
(List (llvm.ident × llvm_type × BlockLabelValMap)
 × List llvm.stmt) 
| prev, (⟨Option.some nm, (llvm.instruction.phi lTy valLbs), _⟩::rest) =>
let lblAndVals := valLbs.toList.map (λ p => (p.snd,p.fst));
let valMap := RBMap.fromList lblAndVals (λ x y => x < y);
extractPhiStmtVars ((nm, lTy, valMap)::prev) rest
| prev, rest => (prev, rest)

/-- Builds an RBMap from a list with llvm.ident keys. --/
def llvmIdentRBMap {α : Type} (entries: List (llvm.ident × α))
 : RBMap llvm.ident α (λ (x y:llvm.ident)=> x<y) :=
RBMap.fromList entries (λ (x y:llvm.ident)=> x<y)

/-- Used to parse a single basic block's annotation in a function annotation. --/
def parseAnnotatedBlock
(fnm:FnName) -- ^ Function whose block is being parsed.
(blockMap:RBMap llvm.ident Json (λ x y => x<y)) -- ^ Block label to block annotation map.
(b:llvm.basic_block) -- ^ Basic block of `fnm`.
: ModuleVCG AnnotatedBlock := do
let lbl := b.label;
let (phiVarList, llvmStmts) := extractPhiStmtVars [] b.stmts.toList;
let parseLLVMVar : (llvm.ident × llvm_type × BlockLabelValMap) → ModuleVCG (llvm.ident × SMTLIB.sort) :=
  (λ (p : (llvm.ident × llvm_type × BlockLabelValMap)) =>
    let (nm, tp, _) := p;
    match llvmTypeToSort tp with
    | Option.some s => pure (nm, s)
    | Option.none   => blockError fnm lbl $ BlockError.unsupportedPhiVarType nm tp);
llvmVarMap ← llvmIdentRBMap <$> phiVarList.mapM parseLLVMVar;
blockJson ← match blockMap.find? lbl.label with
  | Option.some json => pure json
  | Option.none => blockError fnm lbl BlockError.missingAnnotations;
match parseBlockAnn llvmVarMap blockJson with
| Except.error errMsg => 
  blockError fnm lbl $ BlockError.annParseFailure errMsg
| Except.ok ann => do
  let phiMap := RBMap.empty;
  pure $ {annotation := ann,
          label := lbl,
          phiVarMap := phiMap,
          stmts := llvmStmts
         }

/-- Return the definition in the module with the given name. --/
def getDefineByName (lMod:llvm.module) (name:String) : Option llvm.define :=
lMod.defines.find? (λ d => d.name.symbol == name)


/-- Define LLVM arguments in terms of the function start value of
    machine code registers. --/
def parseLLVMArgs
(fnm:FnName) : -- ^ Name of function for error purposes.
List LLVMMCArgBinding → -- ^ Accumulator for parsed arguments.
List (llvm.typed llvm.ident) → -- ^ Arguments to be parsed.
List x86.Reg64 →  -- ^ Remaining registers available for arguments.
ModuleVCG (List LLVMMCArgBinding)
| revArgs, [], _ => pure revArgs.reverse
| revBinds, (⟨llvm_type.prim_type (prim_type.integer 64), nm⟩::restArgs), regs =>
  match regs with
  | [] => functionError fnm $ FnError.custom $ 
          "Maximum of "++(x86ArgGPRegs.length.repr)++" i64 arguments supported"
  | (reg::restRegs) =>
    let binding := LLVMMCArgBinding.mk nm (SMTLIB.sort.bitvec 64) reg;
    parseLLVMArgs (binding::revBinds) restArgs restRegs
| _, (⟨tp, nm⟩::restArgs), _ =>
  functionError fnm $ FnError.argTypeUnsupported nm tp

/-- Builds a mapping from block labels to corresponding block annotation json objects. --/
def buildBlockAnnMap (fAnn:FunctionAnn) : ModuleVCG (RBMap llvm.ident Json (λ x y => x<y)) := do
let mkEntry : List (llvm.ident × Json) → Json → ModuleVCG (List (llvm.ident × Json)) := 
  λ entries blockAnn => 
    match parseObjValAsString blockAnn "label" with
    | Except.error errMsg => 
      functionError fAnn.llvmFunName $ FnError.custom
      ("Encountered an error while parsing the block annotation: "
      ++ errMsg)
    | Except.ok lbl => pure $ (llvm.ident.named lbl, blockAnn)::entries;
llvmIdentRBMap <$> fAnn.blocks.foldlM mkEntry []



/-- Verify a particular function satisfies its specification. --/
def verifyFunction (lMod:llvm.module) (fAnn: FunctionAnn): ModuleVCG Unit := do
modCtx ← read;
let fnm := fAnn.llvmFunName;
vcgLog $ "Analyzing " ++ fnm;
-- Get the LLVM `define` associated with the function name
lFun ← match getDefineByName lMod fnm with
  | Option.some f => pure f
  | Option.none => functionError fnm FnError.notFound;
-- Parse the LLVM args and assign them to registers
argBindings ← parseLLVMArgs fnm [] lFun.args.toList x86ArgGPRegs;
-- Build a mapping from block labels to the JSON block annotations
blockMap ← buildBlockAnnMap fAnn;
-- Parse each block annotation in the JSON
blocks ← lFun.body.mapM (parseAnnotatedBlock fnm blockMap);
-- Build a mapping from block labels to AnnotatedBlock
let blockMap : RBMap llvm.block_label AnnotatedBlock (λ x y => x<y) := 
  RBMap.fromList (blocks.toList.map (λ ab => (ab.label, ab))) (λ x y => x<y);
-- Verify the first block is where the annotation indicated it should be, and return
-- the label for the first block
entryBlockLbl ← (match lFun.body.toList with
  | [] => functionError fnm FnError.missingEntryBlock
  | (firstBlock :: _) => match blockMap.find? firstBlock.label with
    | Option.none => blockError fnm firstBlock.label BlockError.missingAnnotations
    | Option.some ab => match ab.annotation with
      | BlockAnn.unreachable => functionError fnm FnError.entryUnreachable
      | BlockAnn.reachable firstBlockAnn =>
        match getMCAddrOfLLVMFunction modCtx.symbolAddrMap fnm with
        | Except.error errMsg =>
          -- TODO(AMK) once we actually parse the addresses from the ELF file
          -- we can raise an error if the two addresses don't match
          pure ab.label
          -- functionError fnm $ FnError.custom $ 
          --   "Unable to find function machine code address: " ++ errMsg
        | Except.ok addr =>
          if (addr == firstBlockAnn.startAddr)
          then pure ab.label
          else moduleThrow $ 
               fnm ++ " annotation address listed as " 
                   ++ (firstBlockAnn.startAddr.addr.pp_hex
                   ++ "; symbol table however lists address as " ++ addr.addr.pp_hex ++ "."));
-- Verify each block.
blocks.forM (λ ab => moduleCatch $ verifyBlock fAnn argBindings blockMap entryBlockLbl ab)


/-- Returns the loaded and parsed annotation info and a Prover session based on the given VCGConfig.
    throwing an IO.userError if anything fails. --/
def setupWithConfig (cfg : VCGConfig) : IO (ModuleAnnotations × ProverSessionGenerator) := do
-- Read in the annotation file.
annContents ← IO.FS.readFile cfg.annFile;
modAnn ← elseThrowPrefixed (Lean.Json.parse annContents >>= parseAnnotations)
         $ "Encountered an error while parsing the Json in `"++ cfg.annFile ++"`: ";
when cfg.verbose $
  IO.println $ "Parsed the JSON annotation file `"++cfg.annFile++"` successfully!";
-- Dispatch on the user-requested mode to setup the prover sesstion generator.
match cfg.mode with
-- Default: just use cvc4 with default args.
| VerificationMode.defaultMode => do
  let args := ["--lang=smt2", "--dedicated-eqrange-quant", "--incremental"];
  psGen ← interactiveSMTGenerator cfg.annFile "cvc4" args;
  pure (modAnn, psGen)
-- Use the user-specified solver and args.
| VerificationMode.runSolverMode solverCmd solverArgs => do
  psGen ← interactiveSMTGenerator cfg.annFile "cvc4" solverArgs;
  pure (modAnn, psGen)
-- Output into the specified directory.
| VerificationMode.exportMode outDir => do
  outDirExists ← IO.isDir outDir;
  unless outDirExists $ throw $ IO.userError $ "Output directory `"++outDir++"` does not exists.";
  -- FIXME create the directory if it's missing? (It's not clear there's a lean4 API for that yet)
  let psGen := ProverSessionGenerator.mk (exportModeCallbacks outDir) (pure ());
  pure (modAnn, psGen)
  

/-- Load the elf binary file and check it is a linux x86_64 binary (erroring if not). --/
def loadElf (filePath : String) : 
  IO (elf.ehdr ELF64 × List (elf.phdr ELF64) × elf.elfmem × (RBMap String (elf.word ELF64) Lean.strLt)) := do
fileContents ← elf.read_info_from_file filePath;
match fileContents with
| (⟨ELF64, (hdr, phdrs)⟩, elfMem) => do
  -- Check the Elf file is for a x86_64
  unless (hdr.machine == elf.machine.EM_X86_64) $
    throw $ IO.userError $ 
      "Expected elf header machine type EM_X86_64 but got `"++ hdr.machine.name ++"`.";
  -- Check the Elf file is a linux binary
  unless (hdr.info.osabi == elf.osabi.ELFOSABI_SYSV || hdr.info.osabi == elf.osabi.ELFOSABI_LINUX) $
    throw $ IO.userError $ "Expected Linux binary but got `"++ toString hdr.info.osabi.name ++"`.";
  let fnSymAddrMap := RBMap.empty; -- TODO / FIXME actually get this info from the elf file
  pure (hdr, phdrs, elfMem, fnSymAddrMap)
| (⟨ELF32, _⟩, _) => do
  throw $ IO.userError $ "Expected an elf class for a 64bit machine, not 32bit."


/-- Build a mapping from type names to `some` underlying `llvm_type`
    or `none` if the type is `opaque` --/
def mkLLVMTypeMap(m:llvm.module): LLVMTypeMap :=
let addEntry : LLVMTypeMap → llvm.type_decl → LLVMTypeMap := λ m tdecl => 
  match tdecl.decl with
  | llvm.type_decl_body.opaque => m.insert tdecl.name Option.none
  | llvm.type_decl_body.defn t => m.insert tdecl.name $ Option.some t;
m.types.foldl addEntry RBMap.empty

/-- Run a ReoptVCG instance w.r.t. the given configuration. --/
def runVCG (cfg : VCGConfig) : IO UInt32 := do
(ann, gen) ← setupWithConfig cfg;
-- Load Elf file and emit warnings
(elfHdr, prgmHdrs, elfMem, fnSymAddrMap) ← loadElf ann.binFilePath;
-- Get LLVM module
lMod ← loadLLVMModule ann.llvmFilePath;
-- Create verification coontext for module.
errorRef ← IO.mkRef 0;
let modCtx : ModuleVCGContext := 
  { annotations := ann
  , memory := elfMem
  , symbolAddrMap := fnSymAddrMap
  , writeStderr := true
  , errorCount := errorRef
  , proverGen := gen
  , moduleTypeMap := mkLLVMTypeMap lMod
  };
-- Run verification.
_ ← runModuleVCG modCtx (do
  ann.functions.forM (λ funAnn => do
    moduleCatch $ verifyFunction lMod funAnn));
-- print out results
errorCnt ← errorRef.get;
if errorCnt > 0 then do
  _ ← IO.println "Errors during verification.";
  pure 1
else do
  _ ← gen.sessionComplete;
  pure 0

end ReoptVCG
