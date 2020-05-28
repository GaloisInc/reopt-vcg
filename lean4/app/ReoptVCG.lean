import LeanLLVM.AST
import LeanLLVM.LLVMLib
import Main.Elf
import ReoptVCG.Annotations
import ReoptVCG.Types
import SMTLIB.Syntax


namespace ReoptVCG

open elf.elf_class

def exportModeCallbacks {α : Type} (outDir : String) (fn : FunctionName) (lbl : BlockLabel) (action : ProverInterface → IO α) : IO α :=
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
def loadElf (filePath : String) : IO (elf.ehdr ELF64 × List (elf.phdr ELF64) × elf.elfmem) := do
fileContents ← elf.read_info_from_file filePath;
match fileContents with
| (⟨ELF32, _⟩, _) => do
  throw $ IO.userError $ "Expected an elf class for a 64bit machine, not 32bit."
| (⟨ELF64, (hdr, phdrs)⟩, elfMem) => do
  -- Check the Elf file is for a x86_64
  unless (hdr.machine == elf.machine.EM_X86_64) $
    throw $ IO.userError $ "Expected elf header machine type EM_X86_64 but got `"++ hdr.machine.name ++"`.";
  -- Check the Elf file is a linux binary
  unless (hdr.info.osabi == elf.osabi.ELFOSABI_SYSV || hdr.info.osabi == elf.osabi.ELFOSABI_LINUX) $
    throw $ IO.userError $ "Expected Linux binary but got `"++ toString hdr.info.osabi.name ++"`.";
  pure (hdr, phdrs, elfMem)


/-- Load the LLVM module in the given file. --/
def loadLLVMModule (filePath : String) : IO llvm.module := do
ctx ← llvm.ffi.newContext;
mb ← llvm.ffi.newMemoryBufferFromFile filePath;
b ← llvm.ffi.parseBitcodeFile mb ctx;
llvm.loadModule b

/-- Run a ReoptVCG instance w.r.t. the given configuration. --/
def runVCG (cfg : VCGConfig) : IO UInt32 := do
(ann, gen) ← setupWithConfig cfg;
-- Load Elf file and emit warnings
(elfHdr, prgmHdrs, elfMem) ← loadElf ann.binFilePath;
-- Get LLVM module
lMod ← loadLLVMModule ann.llvmFilePath;
-- Create verification coontext for module.
errorRef ← IO.mkRef 0;
-- BOOKMARK populate ModuleVCGContext w/ data from elf and llvm info,
-- fixing ModuleVCGContext types where needed.
let modCtx : ModuleVCGContext := 
  { annotations := ann
  , memory := elfMem
  -- FIXME do we need to parse this info from the elf file before this point?
  , symbolAddrMap := RBMap.empty --Map.fromList
                    --[ (memSymbolName sym, memSymbolStart sym)
                    --| sym <- symbols
                    --]
  , writeStderr := true
  , errorCount := errorRef
  , proverGen := gen
  , moduleTypeMap := RBMap.empty -- Map.fromList
      -- [ (nm,tp)
      -- | L.TypeDecl nm tp <- L.modTypes lMod
      -- ]
  };
pure 0

-- -- Run verification.
-- runModuleVCG modCtx $ do
--   forM_ (Ann.functions ann) $ \funAnn -> do
--     moduleCatch $ verifyFunction lMod funAnn
-- -- print out results
-- errorCnt <- readIORef errorRef
-- if errorCnt > 0 then do
--   hPutStrLn stderr "Errors during verification."
--   exitFailure
--  else
--   sessionComplete gen
  

end ReoptVCG
