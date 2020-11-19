import Galois.Init.Json
import LeanLLVM.AST
import ReoptVCG.Elf
import ReoptVCG.Annotations
import ReoptVCG.VCGBlock
import ReoptVCG.LoadLLVM
import ReoptVCG.Smt
import ReoptVCG.Types
import SmtLib.Smt
import X86Semantics.Common
import DecodeX86.DecodeX86

namespace ReoptVCG

open Lean (Json strLt)
open Lean.Json (parseObjValAsString)

open elf.elf_class (ELF64)
open LLVM (LLVMType LLVMType.prim LLVMType.ptr PrimType PrimType.integer)

open Smt (SmtSort SmtSort.bitvec SmtSort.bv64)


-- | Use a map from symbol names to address to find address.
def getMCAddrOfLLVMFunction
(m : Std.RBMap String (elf.word ELF64) Lean.strLt)
-- ^ Map from symbol names in machine code
-- to the address in the binary.
(fnm : String)
-- ^ Function name
: Except String MCAddr := do
match m.find? fnm with
| Option.none => throw $ "Cannot find address of LLVM symbol: " ++ fnm
| Option.some expectedAddr => pure $ MCAddr.mk expectedAddr


def llvmTypeToSort : LLVMType → Option SmtSort
| LLVMType.prim (PrimType.integer lw) =>
  Option.some $ SmtSort.bitvec lw
| LLVMType.ptr _ => Option.none
| _ => Option.none



/- Verify a block satisfies its specification. -/
def verifyBlock
  (funAnn : FunctionAnn)
   -- ^ Annotations for function
  (argBindings : List LLVMMCArgBinding)
  (blockMap : ReachableBlockAnnMap)
  -- ^ Annotations on blocks.
  (firstLabel : LLVM.BlockLabel)
   -- ^ Label of first block.
  (firstAddr : MCAddr)
   -- ^ Address of first block.
  (aBlock : AnnotatedBlock)
  : ModuleVCG BlockVerificationEvent := do
  -- Get annotations for this block
  match aBlock.annotation with
  -- We only need to verify unreachable blocks are not reachable.
  | BlockAnn.unreachable =>
    pure $ BlockVerificationEvent.block $
     {llvmFunName := funAnn.llvmFunName,
      blockLbl := aBlock.label,
      blockVerificationEvents := []}
  | BlockAnn.reachable blockAnn => do
    -- Check allocations do not overlap with each other.
    -- FIXME we're ignoring alloca stuff for now, FYI
    -- checkAllocaOverlap aBlock.label (Map.elems (Ann.blockAllocas blockAnn))
    -- Start running verification condition generator.
    let mCtx ← read;
    let verify : BlockVCG Unit := verifyReachableBlock blockAnn argBindings aBlock.phiVarMap aBlock.stmts;
    match verify.run mCtx funAnn blockMap firstLabel firstAddr aBlock.label blockAnn with
    | Except.ok vEvents => 
      pure $ BlockVerificationEvent.block $
        {llvmFunName := funAnn.llvmFunName,
         blockLbl := aBlock.label,
         blockVerificationEvents := vEvents}
    | Except.error (BlockVCGError.localErr e) => do
      modify (λ s => {s with errorCount := s.errorCount + 1});
      pure $ BlockVerificationEvent.error funAnn.llvmFunName aBlock.label e
    | Except.error (BlockVCGError.globalErr msg) =>
      throw $ ModuleError.fatal msg



/- Extract the phi statements from the list of statements, returning
   either the name of the variable and type that could not be interpreted
   or a map from from variable names to their types. -/
def extractPhiStmtVars : 
List (LLVM.Ident × LLVMType × BlockLabelValMap) →
List LLVM.Stmt →
(List (LLVM.Ident × LLVMType × BlockLabelValMap)
 × List LLVM.Stmt)
| prev, (⟨Option.some nm, (LLVM.Instruction.phi lTy valLbs), _⟩::rest) =>
  let lblAndVals := valLbs.toList.map (λ p => (p.snd,p.fst));
  let valMap := Std.RBMap.fromList lblAndVals (λ x y => x < y);
  extractPhiStmtVars ((nm, lTy, valMap)::prev) rest
| prev, rest => (prev, rest)

/- Builds an RBMap from a list with LLVM.Ident keys. -/
def llvmIdentRBMap {α : Type} (entries: List (LLVM.Ident × α))
 : Std.RBMap LLVM.Ident α (λ (x y:LLVM.Ident)=> x<y) :=
Std.RBMap.fromList entries (λ (x y:LLVM.Ident)=> x<y)

/- Used to parse a single basic block's annotation in a function annotation. -/
def parseAnnotatedBlock
  (fnm:FnName) -- ^ Function whose block is being parsed.
  (blockMap:Std.RBMap LLVM.Ident Json (λ x y => x<y)) -- ^ Block label to block annotation map.
  (b:LLVM.BasicBlock) -- ^ Basic block of `fnm`.
  : ModuleVCG AnnotatedBlock := do
  let lbl := b.label;
  let (phiVarList, llvmStmts) := extractPhiStmtVars [] b.stmts.toList;
  let parseLLVMVar : (LLVM.Ident × LLVMType × BlockLabelValMap) → ModuleVCG (LLVM.Ident × SmtSort) :=
    (λ (p : (LLVM.Ident × LLVMType × BlockLabelValMap)) =>
      let (nm, tp, _) := p;
      match llvmTypeToSort tp with
      | Option.some s => pure (nm, s)
      | Option.none   => blockError fnm lbl $ BlockError.unsupportedPhiVarType nm tp);
  let varTypes ← phiVarList.mapM parseLLVMVar;
  let llvmTyEnv := Std.RBMap.ltMap varTypes;
  let blockJson ← match blockMap.find? lbl.label with
    | Option.some json => pure json
    | Option.none => blockError fnm lbl BlockError.missingAnnotations;
  match parseBlockAnn llvmTyEnv blockJson with
  | Except.error errMsg => 
    blockError fnm lbl $ BlockError.annParseFailure errMsg
  | Except.ok ann => do
    let phiMap := Std.RBMap.ltMap phiVarList;
    pure $ {annotation := ann,
            label := lbl,
            phiVarMap := phiMap,
            stmts := llvmStmts
           }

/- Return the definition in the module with the given name. -/
def getDefineByName (lMod:LLVM.Module) (name:String) : Option LLVM.Define :=
  lMod.defines.find? (λ d => d.name.symbol == name)


/- Define LLVM arguments in terms of the function start value of
   machine code registers. -/
def parseLLVMArgs
  (fnm:FnName) : -- ^ Name of function for error purposes.
  List LLVMMCArgBinding → -- ^ Accumulator for parsed arguments.
  List (LLVM.Typed LLVM.Ident) → -- ^ Arguments to be parsed.
  List x86.reg64 →  -- ^ Remaining registers available for arguments.
  ModuleVCG (List LLVMMCArgBinding)
| revArgs, [], _ => pure revArgs.reverse
| revBinds, (⟨LLVMType.prim (PrimType.integer 64), nm⟩::restArgs), regs =>
  match regs with
  | [] => functionError fnm $ FnError.custom $ 
          "Maximum of "++(x86ArgGPRegs.length.repr)++" i64 arguments supported"
  | (reg::restRegs) =>
    let binding := LLVMMCArgBinding.mk nm (SmtSort.bv64) reg;
    parseLLVMArgs fnm (binding::revBinds) restArgs restRegs
| _, (⟨tp, nm⟩::restArgs), _ =>
  functionError fnm $ FnError.argTypeUnsupported nm tp

/- Builds a mapping from block labels to corresponding block annotation json objects. -/
def buildBlockAnnMap (fAnn:FunctionAnn) : ModuleVCG (Std.RBMap LLVM.Ident Json (λ x y => x<y)) := do
let mkEntry : List (LLVM.Ident × Json) → Json → ModuleVCG (List (LLVM.Ident × Json)) :=
  λ entries blockAnn => 
    match parseObjValAsString blockAnn "label" with
    | Except.error errMsg => 
      functionError fAnn.llvmFunName $ FnError.custom
      ("Encountered an error while parsing the block annotation: "
      ++ errMsg)
    | Except.ok lbl => pure $ (LLVM.Ident.named lbl, blockAnn)::entries;
llvmIdentRBMap <$> fAnn.blocks.foldlM mkEntry []



/- Verify a particular function satisfies its specification. -/
def verifyFunction' (lMod:LLVM.Module) (fAnn: FunctionAnn): ModuleVCG FnVerificationEvent := do
  let modCtx ← read;
  let fnm := fAnn.llvmFunName;
  -- Get the LLVM `define` associated with the function name
  let lFun ← match getDefineByName lMod fnm with
    | Option.some f => pure f
    | Option.none => functionError fnm FnError.notFound;
  -- Parse the LLVM args and assign them to registers
  let argBindings ← parseLLVMArgs fnm [] lFun.args.toList x86ArgGPRegs;
  -- Build a mapping from block labels to the JSON block annotations
  let blockMap ← buildBlockAnnMap fAnn;
  -- Parse each block annotation in the JSON
  let blocks ← lFun.body.mapM (parseAnnotatedBlock fnm blockMap);
  -- Build a mapping from block labels to AnnotatedBlock
  let blockMap : Std.RBMap LLVM.BlockLabel AnnotatedBlock (λ x y => x<y) :=
    Std.RBMap.fromList (blocks.toList.map (λ ab => (ab.label, ab))) (λ x y => x<y);
  -- Verify the first block is where the annotation indicated it should be, and return
  -- the label for the first block
  let (entryBlockLbl, entryBlockAddr) ← (match lFun.body.toList with
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
            pure (ab.label, MCAddr.mk (UInt64.ofNat 0))
            -- functionError fnm $ FnError.custom $ 
            --   "Unable to find function machine code address: " ++ errMsg
          | Except.ok addr =>
            if (addr == firstBlockAnn.startAddr)
            then pure (ab.label, addr)
            else moduleThrow $ 
                 fnm ++ " annotation address listed as " 
                     ++ (firstBlockAnn.startAddr.addr.pp_hex
                     ++ "; symbol table however lists address as " ++ addr.addr.pp_hex ++ "."));
  -- Verify each block.
  let bvEvents ← blocks.toList.mapM (verifyBlock fAnn argBindings blockMap entryBlockLbl entryBlockAddr);
  pure $ FnVerificationEvent.fn fnm bvEvents

def verifyFunction (lMod:LLVM.Module) (fAnn: FunctionAnn) : ModuleVCG FnVerificationEvent :=
  let handler : ModuleError → ModuleVCG FnVerificationEvent :=
    λ e => match e with
           | ModuleError.function fnm e => pure $ FnVerificationEvent.error fnm e
           | _ => throw e;
  tryCatch (verifyFunction' lMod fAnn) handler



/- Returns the loaded and parsed annotation info and a Prover session based on the given VCGConfig.
   throwing an IO.userError if anything fails. -/
def setupWithConfig (cfg : VCGConfig) : IO (ModuleAnnotations × ProverSession) := do
  -- Read in the annotation file.
  let annContents ← IO.FS.readFile cfg.annFile;
  let modAnn ← elseThrowPrefixed (Lean.Json.parse annContents >>= parseAnnotations)
           $ "Encountered an error while parsing the Json in `"++ cfg.annFile ++"`: ";
  when cfg.verbose $
    IO.println $ "Parsed the JSON annotation file `"++cfg.annFile++"` successfully!";
  -- Dispatch on the user-requested mode to setup the prover sesstion generator.
  match cfg.mode with
  -- Default: just use cvc4 with default args.
  | VerificationMode.defaultMode => do
    let ps ← interactiveProverSession cfg.annFile "cvc4" defaultCVC4Args;
    pure (modAnn, ps)
  -- Use the user-specified solver and args.
  | VerificationMode.runSolverMode solverCmd solverArgs => do
    let ps ← interactiveProverSession cfg.annFile solverCmd solverArgs;
    pure (modAnn, ps)
  -- Output into the specified directory.
  | VerificationMode.exportMode outDir => do
    let outDirExists ← IO.isDir outDir;
    unless outDirExists do 
      throw $ IO.userError $ "Output directory `"++outDir++"` does not exists.";
    -- FIXME create the directory if it's missing? (It's not clear there's a lean4 API for that yet)
    let ps ← exportProverSession outDir;
    pure (modAnn, ps)
  

/- Load the elf binary file and check it is a linux x86_64 binary (erroring if not). -/
def loadElf (filePath : String) : 
  IO (elf.ehdr ELF64 × List (elf.phdr ELF64) × elf.elfmem × (Std.RBMap String (elf.word ELF64) Lean.strLt)) := do
  let fileContents ← elf.read_info_from_file filePath;
  match fileContents with
  | (⟨ELF64, (hdr, phdrs)⟩, elfMem) => do
    -- Check the Elf file is for a x86_64
    unless (hdr.machine == elf.machine.EM_X86_64) do
      throw $ IO.userError $ 
        "Expected elf header machine type EM_X86_64 but got `"++ hdr.machine.name ++"`.";
    -- Check the Elf file is a linux binary
    unless (hdr.info.osabi == elf.osabi.ELFOSABI_SYSV
            || hdr.info.osabi == elf.osabi.ELFOSABI_LINUX
            || hdr.info.osabi == elf.osabi.ELFOSABI_FREEBSD) do
      throw $ IO.userError $ "Expected Linux binary but got `"++ toString hdr.info.osabi.name ++"`.";
    let fnSymAddrMap := Std.RBMap.empty; -- TODO / FIXME actually get this info from the elf file
    pure (hdr, phdrs, elfMem, fnSymAddrMap)
  | (⟨ELF32, _⟩, _) => do
    throw $ IO.userError $ "Expected an elf class for a 64bit machine, not 32bit."


/- Build a mapping from type names to `some` underlying `LLVMType`
   or `none` if the type is `opaque` -/
def mkLLVMTypeMap(m:LLVM.Module): LLVMTypeMap :=
  let addEntry : LLVMTypeMap → LLVM.TypeDecl → LLVMTypeMap := λ m tdecl =>
    match tdecl.decl with
    | LLVM.TypeDeclBody.opaque => m.insert tdecl.name Option.none
    | LLVM.TypeDeclBody.defn t => m.insert tdecl.name $ Option.some t;
  m.types.foldl addEntry Std.RBMap.empty

def get_text_segment {c} (e : elf.ehdr c) (phdrs : List (elf.phdr c)) : Option (elf.phdr c) :=
  phdrs.find? (fun p => p.flags.has_X)

def runVerificationEvent (ps : ProverSession) : VerificationEvent → IO Unit
| VerificationEvent.msg vMsg => IO.println vMsg.msg
| VerificationEvent.goal vg => ps.verifyGoal vg

def runBlockVerificationEvent (ps : ProverSession) : BlockVerificationEvent → IO Unit
| BlockVerificationEvent.block bv => bv.blockVerificationEvents.forM (runVerificationEvent ps)
| BlockVerificationEvent.error fnm blockLbl bError =>
  IO.println $ "Error while verifying block `" ++ (ppLLVM blockLbl) ++ "` of function `"++ fnm ++"`: " ++ (BlockError.pp bError)


def runFnVerificationEvent (ps : ProverSession) : FnVerificationEvent → IO Unit
| FnVerificationEvent.fn fnm bvEvents => do
  IO.println $ "Analyzing `" ++ fnm ++ "`";
  bvEvents.forM (runBlockVerificationEvent ps)
| FnVerificationEvent.error fnm err =>
  IO.println $ "Error while verifying funcion `" ++ fnm ++ "`: " ++ (FnError.pp err)

/- Run a ReoptVCG instance w.r.t. the given configuration. -/
def runVCG (cfg : VCGConfig) : IO UInt32 := do
  let (ann, proverSession) ← setupWithConfig cfg;
  -- Load Elf file and emit warnings
  -- FIXME: cleanup
  when cfg.verbose $ IO.println $ "Loading Elf file at `" ++ ann.binFilePath ++ "`...";
  let (elfHdr, prgmHdrs, elfMem, fnSymAddrMap) ← loadElf ann.binFilePath;
  when cfg.verbose $ IO.println $ "Elf file loaded!";
  let text_phdr <- (match get_text_segment elfHdr prgmHdrs with
                | none     => throw $ IO.userError $ "No executable segment"
                | (some p) => pure p);
  let text_bytes <- (match elfMem.lookup_buffer (bitvec.of_nat 64 text_phdr.vaddr.toNat) with
                | none        => throw $ IO.userError $ "No text region"
                | some (_, b) => pure b);
  let entry := elfHdr.entry.toNat;
  let d := decodex86.mk_decoder text_bytes text_phdr.vaddr.toNat;
  when cfg.verbose $ IO.println $ "x86 decoder built...";
  -- Get LLVM module
  when cfg.verbose $ IO.println $ "Loading LLVM module at `"++ann.llvmFilePath++"`";
  let lMod ← loadLLVMModule ann.llvmFilePath;
  when cfg.verbose $ IO.println $ "LLVM module loaded!";
  -- Create verification coontext for module.
  let modCtx : ModuleVCGContext :=
    { annotations := ann
    , decoder := d
    , symbolAddrMap := fnSymAddrMap
    , moduleTypeMap := mkLLVMTypeMap lMod
    };
  -- Run verification.
  when cfg.verbose $ IO.println $ "Compiling VCG data for the module...";
  let verifyFns := ann.functions.mapM (verifyFunction lMod);
  let (fvEvents, mState) ←
    match runModuleVCG modCtx verifyFns with
    | Except.ok res => pure res
    | Except.error e =>
      throw $ IO.userError $ "Fatal error encountered while constructing verification for functions: " ++ (ModuleError.pp e);
  when cfg.verbose $ IO.println $ "Running VCG for the module...";
  fvEvents.forM (runFnVerificationEvent proverSession);
  -- print out results
  if mState.errorCount > 0 then do
    proverSession.sessionComplete;
    IO.println (repr mState.errorCount ++ " errors were encountered.");
    pure 1
  else
    proverSession.sessionComplete

end ReoptVCG
