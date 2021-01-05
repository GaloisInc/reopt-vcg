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

import ReoptVCG.Translate

import MCInst.Basic
import ReoptVCG.KTranslate

-- FIXME: move
namespace x86
namespace manual_semantics

def mkSemantics (text_bytes : ByteArray) (vaddr : Nat) : x86.vcg.Semantics :=
  let d := decodex86.mk_decoder text_bytes vaddr;  
  { instruction := decodex86.instruction, 
    instruction_size := fun i => i.nbytes,
    decode           := fun n => match decodex86.decode d n with 
                                 | Sum.inl _ => Sum.inl "Unknown"
                                 | Sum.inr r => Sum.inr r,
    eval             := eval_instruction     
  }
end manual_semantics
end x86

namespace x86
namespace mcinst

def mkSemantics (text_bytes : ByteArray) (vaddr : Nat) : x86.vcg.Semantics :=
  let d := mk_decoder text_bytes vaddr;  
  { instruction := instruction × Nat, 
    instruction_size := fun i => i.snd,
    decode           := fun n => match decode d n with 
                                 | Sum.inl _ => Sum.inl "Unknown"
                                 | Sum.inr r => Sum.inr r,
    eval             := fun backend i => eval_instruction backend i.fst
  }

end mcinst
end x86


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
      modify (λ s => {s with blockErrors := e::s.blockErrors})
      pure $ BlockVerificationEvent.error e
    | Except.error (BlockVCGError.globalErr msg) =>
      moduleThrow {fnName := some funAnn.llvmFunName,
                   blockLbl := aBlock.label} 
                  ModuleErrorTag.fatal
                  msg



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
  let parseLLVMVar : (LLVM.Ident × LLVMType × BlockLabelValMap) → 
                     ModuleVCG (LLVM.Ident × SmtSort) :=
      λ (p : (LLVM.Ident × LLVMType × BlockLabelValMap)) =>
      let (nm, tp, _) := p
      match llvmTypeToSort tp with
      | Option.some s => pure (nm, s)
      | Option.none   => 
        moduleThrow {fnName := some fnm,
                     blockLbl := some lbl}
                    ModuleErrorTag.unsupportedPhiVarType
                    (nm.asString ++ " : " ++ ppLLVM tp)
  let varTypes ← phiVarList.mapM parseLLVMVar;
  let llvmTyEnv := Std.RBMap.ltMap varTypes;
  let blockJson ← match blockMap.find? lbl.label with
    | Option.some json => pure json
    | Option.none => 
      moduleThrow {fnName := some fnm,
                     blockLbl := some lbl}
                  ModuleErrorTag.blockMissingAnnotations
                  ""
  match parseBlockAnn llvmTyEnv blockJson with
  | Except.error errMsg => 
    moduleThrow {fnName := some fnm,
                 blockLbl := some lbl}
                ModuleErrorTag.annParseFailure
                errMsg
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
  | [] => 
    let maxArgs : Nat := x86ArgGPRegs.length
    let totalArgs : Nat := maxArgs + 1 + restArgs.length
    moduleThrow {fnName := some fnm, blockLbl := none}
                ModuleErrorTag.maxFnArgCntSurpassed 
                ((repr maxArgs)++" supported, but got "++(repr totalArgs))
  | (reg::restRegs) =>
    let binding := LLVMMCArgBinding.mk nm (SmtSort.bv64) reg;
    parseLLVMArgs fnm (binding::revBinds) restArgs restRegs
| _, (⟨tp, nm⟩::restArgs), _ =>
  moduleThrow {fnName := some fnm, blockLbl := none}
              ModuleErrorTag.argTypeUnsupported
              (nm.asString++ " : "++ppLLVM tp)

/- Builds a mapping from block labels to corresponding block annotation json objects. -/
def buildBlockAnnMap (fAnn:FunctionAnn) : ModuleVCG (Std.RBMap LLVM.Ident Json (λ x y => x<y)) := do
let mkEntry : List (LLVM.Ident × Json) → Json → ModuleVCG (List (LLVM.Ident × Json)) :=
  λ entries blockAnn => 
    match parseObjValAsString blockAnn "label" with
    | Except.error errMsg =>
      moduleThrow {fnName := some fAnn.llvmFunName, blockLbl := none}
                  ModuleErrorTag.annParseFailure
                  errMsg
    | Except.ok lbl => pure $ (LLVM.Ident.named lbl, blockAnn)::entries;
llvmIdentRBMap <$> fAnn.blocks.foldlM mkEntry []



/- Verify a particular function satisfies its specification. -/
def verifyFunction' (lMod:LLVM.Module) (fAnn: FunctionAnn): ModuleVCG FnVerificationEvent := do
  let modCtx ← read;
  let fnm := fAnn.llvmFunName;
  -- Get the LLVM `define` associated with the function name
  let lFun ← match getDefineByName lMod fnm with
    | Option.some f => pure f
    | Option.none => 
      moduleThrow {fnName := fnm, blockLbl := none}
                  ModuleErrorTag.fnNotFound
                  ""
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
  let (entryBlockLbl, entryBlockAddr) ← match lFun.body.toList with
    | [] => moduleThrow {fnName := fnm, blockLbl := none}
                        ModuleErrorTag.missingEntryBlock
                        ""
    | (firstBlock :: _) => match blockMap.find? firstBlock.label with
      | Option.none => 
        moduleThrow {fnName := fnm, blockLbl := firstBlock.label}
                    ModuleErrorTag.blockMissingAnnotations
                    ""
      | Option.some ab => match ab.annotation with
        | BlockAnn.unreachable => 
          moduleThrow {fnName := fnm, blockLbl := none}
                      ModuleErrorTag.entryUnreachable
                      ""
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
            else moduleThrow {fnName := fnm, blockLbl := ab.label}
                             ModuleErrorTag.fnAnnAddrWrong
                             ("annotation address "++ firstBlockAnn.startAddr.addr.pp_hex
                              ++", symbol table address "++addr.addr.pp_hex)
  -- Verify each block.
  let bvEvents ← blocks.toList.mapM (verifyBlock fAnn argBindings blockMap entryBlockLbl entryBlockAddr);
  pure $ FnVerificationEvent.fn fnm bvEvents

def verifyFunction (lMod:LLVM.Module) (fAnn: FunctionAnn) : ModuleVCG FnVerificationEvent :=
  let handler : ModuleError → ModuleVCG FnVerificationEvent :=
    λ e => match e.tag with
           | ModuleErrorTag.fatal => throw e
           | _ => do
             modify (λ s => {s with moduleErrors := e :: s.moduleErrors})
             pure $ FnVerificationEvent.error e
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

def runVerificationEvent (cfg : VCGConfig) (ps : ProverSession) : VerificationEvent → IO Unit
| VerificationEvent.msg vMsg => do
  IO.println $ ""
  IO.println $ vMsg.msg
| VerificationEvent.goal vg =>
  ps.verifyGoal cfg vg

def runBlockVerificationEvent (cfg : VCGConfig) (ps : ProverSession) : BlockVerificationEvent → IO Bool
| BlockVerificationEvent.block bv => do
  bv.blockVerificationEvents.forM (runVerificationEvent cfg ps)
  pure true
| BlockVerificationEvent.error err => do
  IO.println $ ""
  IO.println $ "Error during block verification condition generation: " ++ err.pp
  pure false


def runFnVerificationEvent (cfg : VCGConfig) (ps : ProverSession) (errCnt : IO.Ref Nat) : FnVerificationEvent → IO Unit
| FnVerificationEvent.fn fnm bvEvents => do
  IO.println $ ""
  IO.println $ "Analyzing `" ++ fnm ++ "`"
  let failure : Bool := false
  for e in bvEvents do
    let success ← runBlockVerificationEvent cfg ps e
    if !success then do
      failure := true
  if failure then do
    errCnt.modify Nat.succ
| FnVerificationEvent.error err => do
  IO.println $ ""
  IO.println $ "Error during function verification condition generation: " ++ err.pp

def reportErrors (bErrors : List BlockError) (mErrors : List ModuleError) (success : Bool) : IO UInt32 := do
  let indent : String := "  "
  -- summarize block errors
  let bErrCnt : Nat := 0
  if !bErrors.isEmpty then do
    IO.println ""
    IO.println "======================= ERRORS ======================="
    let bErrMap : Std.RBMap BlockErrorTag (Nat × (Std.RBMap String Nat (λ x y => x < y))) BlockErrorTag.lt := Std.RBMap.empty
    for err in bErrors do
      bErrCnt := bErrCnt + 1
      bErrMap := let (tagCnt, tagMap) := bErrMap.findD err.tag (0, Std.RBMap.empty)
                 let extraInfoCount := tagMap.findD err.extraInfo 0
                 bErrMap.insert err.tag (tagCnt + 1, (tagMap.insert err.extraInfo (extraInfoCount + 1)))
    if bErrCnt > 0 then do
      IO.println $ ""
      IO.println $ (repr bErrCnt)++" block errors encountered:"
      for (tag, (tagCnt, tagMap)) in bErrMap.toList do -- FIXME remove toList next lean bump
        IO.println $ indent++"* ("++(repr tagCnt)++") "++tag.description
        for (extraInfo, n) in tagMap.toList do -- FIXME remove toList next lean bump
          IO.println $ indent++indent++"- ("++(repr n)++") "++extraInfo
  -- summarize module errors
  let mErrCnt : Nat := 0
  if !mErrors.isEmpty then do
    let mErrMap : Std.RBMap ModuleErrorTag (Nat × (Std.RBMap String Nat (λ x y => x < y))) ModuleErrorTag.lt := Std.RBMap.empty
    for err in mErrors do
      mErrCnt := mErrCnt + 1
      mErrMap := let (tagCnt, tagMap) := mErrMap.findD err.tag (0, Std.RBMap.empty)
                 let extraInfoCount := tagMap.findD err.extraInfo 0
                 mErrMap.insert err.tag (tagCnt + 1, (tagMap.insert err.extraInfo (extraInfoCount + 1)))
    IO.println $ ""
    IO.println $ (repr mErrCnt)++" module errors encountered:"
    for (tag, (tagCnt, tagMap)) in mErrMap.toList do -- FIXME remove toList next lean bump
      IO.println $ indent++"* ("++(repr tagCnt)++") "++tag.description
      for (extraInfo, n) in tagMap.toList do -- FIXME remove toList next lean bump
        IO.println $ indent++indent++"- ("++(repr n)++") "++extraInfo
  if success
  then pure 1
  else pure $ if bErrCnt > 0 then 1 else 0

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
  let sem := match cfg.semanticsBackend with
             | SemanticsBackend.KSemantics      => x86.mcinst.mkSemantics text_bytes text_phdr.vaddr.toNat
             | SemanticsBackend.ManualSemantics => x86.manual_semantics.mkSemantics text_bytes text_phdr.vaddr.toNat;
  when cfg.verbose $ IO.println $ "x86 decoder built...";
  -- Get LLVM module
  when cfg.verbose $ IO.println $ "Loading LLVM module at `"++ann.llvmFilePath++"`";
  let lMod ← loadLLVMModule ann.llvmFilePath;
  when cfg.verbose $ IO.println $ "LLVM module loaded!";
  -- Create verification coontext for module.
  let modCtx : ModuleVCGContext :=
    { annotations := ann
    , instructionEvents := x86.vcg.instructionEvents sem
    , symbolAddrMap := fnSymAddrMap
    , moduleTypeMap := mkLLVMTypeMap lMod
    };
  -- Run verification.
  IO.println $ "Generating verification conditions for LLVM module..."
  let verifyFns := ann.functions.mapM (verifyFunction lMod)
  let (fvEvents, mState) ←
    match runModuleVCG modCtx verifyFns with
    | Except.ok res => pure res
    | Except.error e =>
      throw $ IO.userError $ "Fatal error encountered while constructing verification for functions: " ++ (ModuleError.pp e)
  match cfg.mode with
  | VerificationMode.defaultMode =>
    IO.println $ "Default solver mode: checking verification conditions using cvc4..."
  | VerificationMode.runSolverMode solver solverArgs =>
    let cmd := solver ++ (String.intercalate " " solverArgs)
    IO.println $ "Solver mode: checking verification conditions with user-specified solver..."
  | VerificationMode.exportMode path =>
    IO.println $ "Writing out verification conditions as .smt2 files to directory `"++path++"`..."
  let errCntRef ← IO.mkRef 0;
  fvEvents.forM (runFnVerificationEvent cfg proverSession errCntRef)
  let errCnt ← errCntRef.get
  -- print out results
  let {success := success,
       printSummary := printSummary,
       printFailures := printFailures} ← proverSession.sessionComplete
  printSummary
  let okCnt := fvEvents.length - errCnt
  IO.println $ (repr okCnt)++" out of "++(repr (okCnt + errCnt))++" functions successfully analyzed with no errors."
  printFailures
  reportErrors mState.blockErrors mState.moduleErrors success

end ReoptVCG
