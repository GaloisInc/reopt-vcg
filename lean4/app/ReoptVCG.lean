import Galois.Init.Json
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import Main.Elf
import ReoptVCG.Annotations
import ReoptVCG.Types
import SMTLIB.Syntax
import X86Semantics.Common

namespace ReoptVCG

open Lean (Json strLt)
open Lean.Json (parseObjValAsString)

open elf.elf_class (ELF64)
open llvm (llvm_type llvm_type.prim_type prim_type prim_type.integer)

def exportModeCallbacks {α : Type} (outDir : String) (fn : FnName) (lbl : llvm.block_label) (action : ProverInterface → IO α) : IO α :=
-- FIXME
action $ ProverInterface.mk (λ _ => pure ()) (λ _ _ => pure ()) (λ _ _ => pure ())


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


/-- Maps between LLVM argument and machine code name. --/
structure LLVMMCArgBinding :=
(llvmArgName : llvm.ident)
(smtSort: SMTLIB.sort)
(register: x86.Reg64)



/-- Used to parse a single basic block in a function. --/
def parseAnnotatedBlock
(fnm:FnName) -- ^ Function whose block is being parsed.
(blockMap:RBMap String Json strLt) -- ^ Block label to block annotation map.
(b:llvm.basic_block) -- ^ Basic block of `fnm`.
: ModuleVCG AnnotatedBlock :=
blockError fnm b.label BlockError.missingAnnotations -- FIXME / TODO





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
def buildBlockAnnMap (fAnn:FunctionAnn) : ModuleVCG (RBMap String Json strLt) := do
let mkEntry : List (String × Json) → Json → ModuleVCG (List (String × Json)) := 
  λ entries blockAnn => 
    match parseObjValAsString blockAnn "label" with
    | Except.error errMsg => 
      functionError fAnn.llvmFunName $ FnError.custom
      ("Encountered an error while parsing the block annotation: "
      ++ errMsg)
    | Except.ok lbl => pure $ (lbl, blockAnn)::entries;
entries ← fAnn.blocks.foldlM mkEntry [];
pure $ RBMap.fromList entries Lean.strLt



/-- Verify a particular function satisfies its specification. --/
def verifyFunction (lMod:llvm.module) (fAnn: FunctionAnn): ModuleVCG Unit := do
modCtx ← read;
let fnm := fAnn.llvmFunName;
vcgLog $ "Analyzing " ++ fnm;
lFun ← 
  match getDefineByName lMod fnm with
  | Option.some f => pure f
  | Option.none => functionError fnm FnError.notFound;
argBindings ← parseLLVMArgs fnm [] lFun.args.toList x86ArgGPRegs;
blockMap ← buildBlockAnnMap fAnn;
blks ← lFun.body.mapM (parseAnnotatedBlock fnm blockMap);
-- let blkMap = HMap.fromList [ (ppBlock (abLbl ab), ab) | ab <- blks ]
-- case defBody lFun of
--   [] ->
--     functionError fnm FunctionMissingEntryBlock
--   firstBlock:_ -> do
--     let Just entryLabel = bbLabel firstBlock
--     do firstBlockAnn <-
--          case findBlock blkMap entryLabel of
--            Just (Ann.ReachableBlock b, _) ->
--              pure b
--            Just (Ann.UnreachableBlock, _) -> do
--              functionError fnm FunctionEntryUnreachable
--            Nothing ->
--              blockError fnm entryLabel BlockMissingAnnotations
--        let Right addr = getMCAddrOfLLVMFunction (symbolAddrMap modCtx) fnm
--        when (toInteger addr /= toInteger (Ann.blockAddr firstBlockAnn)) $ do
--          moduleThrow $ printf "%s annotations list address of %s; symbol table reports address of %s."
--                              fnm (show (Ann.blockAddr firstBlockAnn)) (show addr)
--     -- Verify the blocks.
--     forM_ blks $ \ab -> do
--       moduleCatch $ verifyBlock funAnn argBindings blkMap entryLabel ab
pure ()


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
    throw $ IO.userError $ "Expected elf header machine type EM_X86_64 but got `"++ hdr.machine.name ++"`.";
  -- Check the Elf file is a linux binary
  unless (hdr.info.osabi == elf.osabi.ELFOSABI_SYSV || hdr.info.osabi == elf.osabi.ELFOSABI_LINUX) $
    throw $ IO.userError $ "Expected Linux binary but got `"++ toString hdr.info.osabi.name ++"`.";
  let fnSymAddrMap := RBMap.empty; -- FIXME actually get this info from elf
  pure (hdr, phdrs, elfMem, fnSymAddrMap)
| (⟨ELF32, _⟩, _) => do
  throw $ IO.userError $ "Expected an elf class for a 64bit machine, not 32bit."


/-- Load the LLVM module in the given file. --/
def loadLLVMModule (filePath : String) : IO llvm.module := do
ctx ← llvm.ffi.newContext;
mb ← llvm.ffi.newMemoryBufferFromFile filePath;
b ← llvm.ffi.parseBitcodeFile mb ctx;
llvm.loadModule b

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
