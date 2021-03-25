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
import ReoptVCG.InstructionEvents

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
open LLVM (LLVMType LLVMType.prim LLVMType.vector LLVMType.ptr PrimType PrimType.integer PrimType.floatType)

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
  : ModuleVCG (Except BlockError BlockVerification) := do
  -- Get annotations for this block
  match aBlock.annotation with
  -- We only need to verify unreachable blocks are not reachable.
  | BlockAnn.unreachable =>
    pure $ Except.ok $
     {llvmFnName := funAnn.llvmFnName,
      blockLbl := aBlock.label,
      goals := #[],
      warnings := #[]}
  | BlockAnn.reachable blockAnn => do
    -- Check allocations do not overlap with each other.
    -- FIXME we're ignoring alloca stuff for now, FYI
    -- checkAllocaOverlap aBlock.label (Map.elems (Ann.blockAllocas blockAnn))
    -- Start running verification condition generator.
    let mCtx ← read;
    let verify : BlockVCG Unit := verifyReachableBlock blockAnn argBindings aBlock.phiVarMap aBlock.stmts;
    match verify.run mCtx funAnn blockMap firstLabel firstAddr aBlock.label blockAnn with
    | Except.ok (goals, warnings) =>
      pure $ Except.ok
        {llvmFnName := funAnn.llvmFnName,
         blockLbl := aBlock.label,
         goals := goals,
         warnings := warnings}
    | Except.error (BlockVCGError.localErr e) => do
      pure $ Except.error e
    | Except.error (BlockVCGError.globalErr msg) =>
      moduleThrow {fnName := some funAnn.llvmFnName,
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
  List x86.avxreg →  -- ^ Remaining float registers available for arguments.
  ModuleVCG (List LLVMMCArgBinding)
| revArgs, [], _, _ => pure revArgs.reverse
| revBinds, (⟨LLVMType.prim (PrimType.integer 64), nm⟩::restArgs), regs, fpregs =>
  match regs with
  | [] =>
    let maxArgs : Nat := x86ArgGPRegs.length
    let totalArgs : Nat := maxArgs + 1 + restArgs.length
    moduleThrow {fnName := some fnm, blockLbl := none}
                ModuleErrorTag.maxFnArgCntSurpassed
                ((reprStr maxArgs)++" word args supported, but got "++(reprStr totalArgs))
  | (reg::restRegs) =>
    let binding := LLVMMCArgBinding.mk nm SmtSort.bv64 (Sigma.mk _ reg);
    parseLLVMArgs fnm (binding::revBinds) restArgs restRegs fpregs
 -- FIXME: Copied from above, maybe merge?
 -- (LLVMType.prim (PrimType.floatType LLVM.FloatType.double)
| revBinds, ( ⟨LLVMType.vector 8 (LLVMType.prim (PrimType.floatType LLVM.FloatType.double)), nm⟩ :: restArgs), regs, fpregs =>
  match fpregs with
  | [] =>
    let maxArgs : Nat := x86ArgFPRegs.length
    let totalArgs : Nat := maxArgs + 1 + restArgs.length
    moduleThrow {fnName := some fnm, blockLbl := none}
                ModuleErrorTag.maxFnArgCntSurpassed
                ((reprStr maxArgs)++" FP args supported, but got "++(reprStr totalArgs))
  | (reg::restFPRegs) =>
    let binding := LLVMMCArgBinding.mk nm (SmtSort.bitvec x86.avx_width) (Sigma.mk _ reg);
    parseLLVMArgs fnm (binding::revBinds) restArgs regs restFPRegs

| _, (⟨tp, nm⟩::restArgs), _, _ =>
  moduleThrow {fnName := some fnm, blockLbl := none}
              ModuleErrorTag.argTypeUnsupported
              (nm.asString++ " : "++ppLLVM tp)

/- Builds a mapping from block labels to corresponding block annotation json objects. -/
def buildBlockAnnMap (fAnn:FunctionAnn) : ModuleVCG (Std.RBMap LLVM.Ident Json (λ x y => x<y)) := do
let mkEntry : List (LLVM.Ident × Json) → Json → ModuleVCG (List (LLVM.Ident × Json)) :=
  λ entries blockAnn =>
    match parseObjValAsString blockAnn "label" with
    | Except.error errMsg =>
      moduleThrow {fnName := some fAnn.llvmFnName, blockLbl := none}
                  ModuleErrorTag.annParseFailure
                  errMsg
    | Except.ok lbl => pure $ (LLVM.Ident.named lbl, blockAnn)::entries;
llvmIdentRBMap <$> fAnn.blocks.foldlM mkEntry []



/- Verify a particular function satisfies its specification. -/
def verifyFunction (lMod:LLVM.Module) (fAnn: FunctionAnn): ModuleVCG FnVerification := do
  let modCtx ← read;
  let fnm := fAnn.llvmFnName;
  -- Get the LLVM `define` associated with the function name
  let lFun ← match getDefineByName lMod fnm with
    | Option.some f => pure f
    | Option.none =>
      moduleThrow {fnName := fnm, blockLbl := none}
                  ModuleErrorTag.fnNotFound
                  ""
  -- Parse the LLVM args and assign them to registers
  let argBindings ← parseLLVMArgs fnm [] lFun.args.toList x86ArgGPRegs x86ArgFPRegs;
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
  let mut blockVCs : Array BlockVerification := #[]
  let mut blockErrors : Array BlockError := #[]
  for b in blocks.toList do -- FIXME remove .toList next bump
    match (← verifyBlock fAnn argBindings blockMap entryBlockLbl entryBlockAddr b) with
    | Except.ok vc => do
      blockVCs := blockVCs.push vc
    | Except.error err => do
      blockErrors := blockErrors.push err
  pure {llvmFnName := fnm,
        blockVCs := blockVCs,
        blockErrors := blockErrors}

def processFns (lMod:LLVM.Module) (anns: List FunctionAnn) : ModuleVCG ModuleVerification := do
  let mut fnVCs := #[]
  let mut moduleErrs := #[]
  for fAnn in anns do
    try do
      let vc ← verifyFunction lMod fAnn
      fnVCs := fnVCs.push vc
    catch err =>
      match err.tag with
      | ModuleErrorTag.fatal => throw err
      | _ => do
        moduleErrs := moduleErrs.push err
  pure {fnVCs := fnVCs,
        errors := moduleErrs}


/- Returns the loaded and parsed annotation info and a Prover session based on the given VCGConfig.
   throwing an IO.userError if anything fails. -/
def setupWithConfig (cfg : VCGConfig) : IO (ModuleAnnotations × VerificationSession) := do
  -- Read in the annotation file.
  let annContents ← IO.FS.readFile cfg.annFile;
  let modAnn ← elseThrowPrefixed (Lean.Json.parse annContents >>= parseAnnotations)
           $ "Encountered an error while parsing the Json in `"++ cfg.annFile ++"`: ";
  when cfg.verbose $
    IO.println $ "Parsed the JSON annotation file `"++cfg.annFile++"` successfully!";
  -- Dispatch on the user-requested mode to setup the prover sesstion generator.
  match cfg.mode with
  -- Solver mode - generates VCs and runs them against SMT
  | VerificationMode.solverMode solverCfg => do
    let (solver, args) := match solverCfg.solverPathAndArgs with
                          | none => ("cvc4", defaultCVC4Args)
                          | some p => p
    let vs ← interactiveVerificationSession cfg.annFile solver args
    pure (modAnn, vs)
  -- Output into the specified directory.
  | VerificationMode.exportMode outDir => do
    let outDirExists ← IO.isDir outDir;
    unless outDirExists do
      throw $ IO.userError $ "Output directory `"++outDir++"` does not exists.";
    -- FIXME create the directory if it's missing? (It's not clear there's a lean4 API for that yet)
    let vs ← exportVerificationSession outDir;
    pure (modAnn, vs)

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

def reportErrors (bErrors : List BlockError) (mErrors : List ModuleError) (success : Bool) : IO UInt32 := do
  let indent : String := "  "
  -- summarize block errors
  let mut bErrCnt : Nat := 0
  if !bErrors.isEmpty then do
    IO.println ""
    IO.println "======================= ERRORS ======================="
    let mut bErrMap : Std.RBMap BlockErrorTag (Nat × (Std.RBMap String Nat (·<·))) (·<·) := Std.RBMap.empty
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
  let mut mErrCnt : Nat := 0
  if !mErrors.isEmpty then do
    let mut mErrMap : Std.RBMap ModuleErrorTag (Nat × (Std.RBMap String Nat (·<·))) (·<·) := Std.RBMap.empty
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

/- Combines a directory with a relative file path.-/
def joinPath (name root p : String) : IO String :=
  if p == "" then
    throw $ IO.userError $ s!"Expected non-empty {name}."
  else if root == "." then
    pure p
  else
   pure $ System.mkFilePath [root, p]

/- Run a ReoptVCG instance w.r.t. the given configuration. -/
def runVCG (cfg : VCGConfig) : IO UInt32 := do
  let annDir := System.FilePath.dirName cfg.annFile
  let (ann, verificationSession) ← setupWithConfig cfg;
  let binPath  ← joinPath "binary filepath" annDir ann.binFilePath
  let llvmPath ← joinPath "llvm filepath"   annDir ann.llvmFilePath
  -- Load Elf file and emit warnings
  -- FIXME: cleanup
  when cfg.verbose $ IO.println $ s!"Loading Elf file at `{binPath}`...";
  let (elfHdr, prgmHdrs, elfMem, fnSymAddrMap) ← loadElf binPath;
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
  when cfg.verbose $ IO.println $ s!"Loading LLVM module at `{llvmPath}`";
  let lMod ← loadLLVMModule llvmPath;
  when cfg.verbose $ IO.println $ "LLVM module loaded!";
  -- Create verification coontext for module.
  let modCtx : ModuleVCGContext :=
    { annotations := ann
    , mkBackendFuns := x86.vcg.mkBackendFuns sem
    , symbolAddrMap := fnSymAddrMap
    , moduleTypeMap := mkLLVMTypeMap lMod
    };
  -- Run verification.
  IO.println $ "Generating verification conditions for LLVM module..."
  let verifyModule := processFns lMod ann.functions
  let mv ← match runModuleVCG modCtx verifyModule with
           | Except.ok res => pure res
           | Except.error e =>
           throw $ IO.userError $ s!"Fatal error encountered while constructing verification for functions: {ModuleError.pp e}"
  verificationSession.verifyModule cfg mv


end ReoptVCG
