
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import LeanLLVM.PP
import SmtLib.Smt
import X86Semantics.Common -- for reg names
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import ReoptVCG.MCStdLib
import ReoptVCG.Smt
import ReoptVCG.ABI

namespace ReoptVCG

open LLVM (LLVMType FloatType Typed PrimType Value)
open Smt (SmtM SmtSort SmtSort.bool SmtSort.bitvec SmtSort.array SmtSort.bv64 IdGen.empty RangeSort.bitvec)
open x86 (reg64)
open BlockVCG (fatalThrow localThrow)
open x86.vcg (RegState)

namespace BlockVCG


def currentLoc : BlockVCG BlockLocation := do
  let fnName ← BlockVCGContext.llvmFnName <$> read
  let lbl ← BlockVCGContext.currentBlock <$> read
  let instrIdx ← BlockVCGState.llvmInstrIndex <$> get
  let curAddr ← BlockVCGState.mcCurAddr <$> get
  pure {fnName := fnName,
        blockLbl := lbl,
        llvmInstrIdx := instrIdx,
        mcAddr := curAddr}

-- | This prepends the LLVM and machine code location information for
-- display to user.
def prependLocation (msg : String) : BlockVCG String := do
  let loc ← currentLoc
  pure $ loc.pp ++": "++msg

def addGoal (g : VerificationGoal) : BlockVCG Unit := do
  modify (λ s => {s with
                    goals := s.goals.push g})


-- | Log a message in the timeline of verification events.
def logWarning (msg : String) : BlockVCG Unit := do
  let loc ← currentLoc
  modify (λ s => {s with warnings := s.warnings.push ⟨loc, msg⟩})


def missingFeature (msg : String) : BlockVCG Unit := do
  logWarning $ "TODO: " ++ msg


-- | Report an error at the given location and stop verification of
-- this block. FIXME this currently uses a callback (which will report an error via IO)
-- _and_ calls `haltBlock`, which will return a local error with an error message. At
-- some point we probably just want to use the latter when we move away from using IO
-- as much.
def fatalBlockError {α} (msg : String) : BlockVCG α := do
  let errMsg ← prependLocation msg;
  fatalThrow errMsg

def localBlockError {α} (err : BlockErrorTag) (extraInfo : String) : BlockVCG α := do
  let loc ← currentLoc
  localThrow {loc := loc, tag := err, extraInfo := extraInfo}

def addCommand (cmd : Smt.Command) : BlockVCG Unit := do
  modify (λ s => {s with smtContext := s.smtContext *> Smt.liftCommand cmd})


def runSmtM {a : Type} (m : SmtM a) : BlockVCG a := do
  let run' := fun (s : BlockVCGState) => 
                  (let r  := Smt.runSmtM s.idGen m;
                       ((r.fst, r.snd.snd.reverse)
                       , {s with idGen := r.snd.fst}));
  let (r, cmds) <- modifyGet run';
  List.forM addCommand cmds;
  pure r

-- | Add assertion that the propositon is true without requiring it to be proven.
def addAssert (p : Smt.Term SmtSort.bool) : BlockVCG Unit := 
  addCommand $ Smt.Command.assert p

-- | @proveTrue prop extraInfo expr@ adds a proof obligation @expr@ is true for all
-- interpretations of constants for the property @prop@ and any @extraInfo@ annotated.
def proveTrue (tag : GoalTag) (extraInfo : String) (expr : Smt.Term SmtSort.bool) : BlockVCG Unit := do
  verifyGoal tag extraInfo expr;
  -- Add command for future proofs
  addAssert expr


def proveEq (tag : GoalTag) (extraInfo : String) {s : SmtSort} (x y : Smt.Term s) : BlockVCG Unit := do
  proveTrue tag extraInfo (Smt.eq x y) -- FIXME ? was proveFalseCallback/Smt.distinct


-- | Add assertion that the propositon is true without requiring it to be proven.
def addComment (str : String) : BlockVCG Unit :=
  addCommand $ Smt.Command.comment str -- FIXME?


def defineRangeCheck (name : String) (low high : Smt.Term SmtSort.bv64)
  : BlockVCG (Smt.Term SmtSort.bv64 -> Smt.Term SmtSort.bv64 -> Smt.Term SmtSort.bool) :=
  runSmtM $ x86.vcg.defineRangeCheck name low high

end BlockVCG

export BlockVCG (addCommand proveTrue proveEq addAssert addComment)

open BlockVCG (localBlockError)

-- open LLVM.LLVMType (HasBVRepr)

--------------------------------------------------------------------------------
-- Type <-> SMT

-- @[reducible]
-- def HasSMTSort : LLVMType -> Prop
-- | LLVM.LLVMType.ptr _  => True
-- | LLVM.LLVMType.prim pt  =>
--   match pt with
--   | LLVM.PrimType.integer i => i > 0
--   | LLVM.PrimType.floatType _ => True
--   | _ => False
-- | LLVM.LLVMType.vector _ ty => HasSMTSort ty
-- | _ => False


-- | Convert LLVM type to SMT sort.
@[reducible]
-- def asSMTSort (tp : LLVMType) (pf : HasBVRepr tp) : SmtSort := 
--   SmtSort.bitvec (tp.nbits pf)

-- def asSMTSort' (tp : LLVMType) : Option SmtSort :=
--   if H : HasBVRepr tp then some (asSMTSort tp H) else none

-- def coerceToSMTSort (ty : LLVMType) : BlockVCG SmtSort :=
--   match asSMTSort' ty with
--   | some tp => pure tp
--   | none    => BlockVCG.fatalBlockError $ "Unexpected type " ++ (ppLLVM ty)

--------------------------------------------------------------------------------
-- Ident <-> SMT

def lookupIdent (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  let m <- BlockVCGState.llvmIdentMap <$> get;
  match m.find? i with
  | some (Sigma.mk s' tm) => 
    if H : s' = s 
    then pure (cast (congrArg Smt.Term H) tm)
    else BlockVCG.fatalBlockError ("Sort mismatch for " ++ i.asString)
  | none => BlockVCG.fatalBlockError ("Unknown ident: " ++ i.asString)

def freshSymbol (n : String) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  let sym <- BlockVCG.runSmtM (Smt.freshSymbol n); -- FIXME: this should be primitive in SMT
  pure (Smt.mkSymbol sym s)

def freshIdent (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  let tm <- freshSymbol i.asString s
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ tm)});
  pure tm

def defineTerm {s : SmtSort} (i : LLVM.Ident) (tm : Smt.Term s) : BlockVCG (Smt.Term s) := do
  let sym <- BlockVCG.runSmtM (Smt.defineFun i.asString [] s tm);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym

def declareTerm (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  let sym <- BlockVCG.runSmtM (Smt.declareFun i.asString [] s);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym


--------------------------------------------------------------------------------
-- MC Events

section

open x86.vcg (Event)
open x86.vcg.Event
open BlockVCG (fatalBlockError localBlockError localThrow fatalThrow)

def mcNextAddr (s : BlockVCGState) : MemAddr := s.mcCurAddr + s.mcCurSize

-- | Get next events
def getNextEvents : BlockVCG Unit := do
  let ctx <- read;
  let s <- get;
  let addr := mcNextAddr s;
  when (not (addr < ctx.mcBlockEndAddr)) $ 
    localBlockError BlockErrorTag.mcRanOutOfEvents "";
  -- FIXMEL df, x87Top
  -- BlockVCG.liftIO $ IO.println ("Decoding at " ++ addr.ppHex);

  addComment ("MC: at " ++ addr.ppHex);

  let (events, idGen', sz) <-
    match ctx.mcInstructionEvents ctx.mcBlockMap s.mcCurRegs s.idGen addr with
    | Except.error e => localBlockError BlockErrorTag.mcInstrEventError e
    | Except.ok    r => pure r;

  -- Update local index and next addr
  set $ { s with idGen := idGen'
               , mcCurAddr := addr
               , mcCurSize := sz
               , mcEvents := events
        }



-- | Set machine code registers from reg state.
def setMCRegs (regs : x86.vcg.RegState) : BlockVCG Unit :=
  -- N.B., the previous Haskell prototype seemed to require Haskell
  -- representatives of the X87_TopReg and DF values which could be passed
  -- to some MC-related (Macaw) functions, but it does not appear we
  -- have any such need heres.
  modify $ fun s => { s with mcCurRegs := regs }


def getSupportedType (s : SmtSort) : BlockVCG (x86.vcg.SupportedMemType s) := do
  let mcstd  <- BlockVCGContext.mcStdLib <$> read;
  let mops := mcstd.memOpsBySort;
  match mops s with
  | some ops => pure ops
  | none => localBlockError BlockErrorTag.unsupportedMemType (toString s)

def declareMem : BlockVCG x86.vcg.memory :=
  BlockVCG.runSmtM $ Smt.declareFun "mem" [] x86.vcg.memory_t

def mcWrite (addr : x86.vcg.memaddr) (s : SmtSort) (val : Smt.Term s) : BlockVCG Unit := do
  let curMem <- (fun (s : BlockVCGState) => s.mcCurMem) <$> get;
  let supType <- getSupportedType s;
  let nextMem <- BlockVCG.runSmtM $ Smt.defineFun "mem" [] x86.vcg.memory_t (supType.writeMem curMem addr val);
  modify $ fun s => { s with mcCurMem := nextMem }

def mcRead (addr : x86.vcg.memaddr) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  let curMem <- BlockVCGState.mcCurMem <$> get;
  let supType <- getSupportedType s;
  pure (supType.readMem curMem addr)

def mcAssignRead (addr : x86.vcg.memaddr) (s : SmtSort) (smtVar : Smt.Term s) : BlockVCG Unit := do
  let v <- mcRead addr s;
  addAssert (Smt.eq smtVar v)

-- | Execute the machine-code only events that occur before jumping to the given address
partial
def execMCOnlyEvents : MemAddr -> BlockVCG Unit
| endAddr => do
  let evts <- BlockVCGState.mcEvents <$> get;
  match evts with
  | Command cmd :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: Command");
      addCommand cmd;
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr
  | Warning msg :: mevs => do
      BlockVCG.logWarning msg;
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr
  | MCOnlyStackReadEvent mcAddr n smtValVar :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: MCOnlyStackReadEvent");
      -- TODO: Fix this to the following

      -- A MCOnlyStack read means the machine code reads memory, but
      -- the llvm does not.
      --
      -- We currently check that these reads only access the stack as
      -- the only current use of these annotations is to mark register
      -- spills, return address read/writes, and frame pointer/callee saved
      -- register saves/restores.
      --
      -- Checking this is on the stack also ensures there are no side effects
      -- from mem-mapped IO reads since the stack should not be mem-mapped IO.

      do let stdLib <- BlockVCGContext.mcStdLib <$> read;
         -- FIXME: assert 8 dvd n
         -- FIMXE: make this take a Nat?
         proveTrue GoalTag.mcOnlyReadFromUnallocStack "" (stdLib.onStack mcAddr (Smt.bvimm _ (n / 8)))

      -- Define value from reading Macaw heap
      mcAssignRead mcAddr (SmtSort.bitvec n) smtValVar;
      -- Process future events.
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr

    -- Every LLVM write should have a machine code write (but not
    -- necessarily vice versa), we pattern match on machine code
    -- writes.
  | MCOnlyStackWriteEvent mcAddr n smtVal :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: MCOnlyStackWriteEvent");

      -- We need to assert that this werite will not be visible to LLVM.

      do let stdLib <- BlockVCGContext.mcStdLib <$> read;
         -- FIXME: assert 8 dvd n
         proveTrue GoalTag.mcOnlyWriteToUnreservedStack "" (stdLib.isInMCOnlyStackRange mcAddr (Smt.bvimm _ (n / 8)))

      -- Update stack with write.
      mcWrite mcAddr (SmtSort.bitvec n) smtVal;
      -- Process next events
      modify $ fun s => {s with mcEvents := mevs };
      execMCOnlyEvents endAddr
    -- This checks to see if the next instruction jumps to the next ip,
    -- and if so it runs it.
  | FetchAndExecuteEvent regs :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: fetch and exec case");
      when (not mevs.isEmpty) $ localBlockError BlockErrorTag.mcEventAfterFetchAndExe ""
      modify $ fun s => { s with mcEvents := [] };
      -- Update registers
      setMCRegs regs;
      -- Process next events
      let nextAddr <- mcNextAddr <$> get;
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: fetch and exec case: " ++ nextAddr.ppHex ++ " " ++ endAddr.ppHex);

      -- FIXME: this is fragile ...
      match Smt.bvAsConst regs.ip with
      | some nextAddr' =>
        if nextAddr = nextAddr' ∧ nextAddr < endAddr
        then do getNextEvents; execMCOnlyEvents endAddr
        else pure ()
      | none => pure ()
  | [] => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: empty case");      
      let nextAddr <- mcNextAddr <$> get;
      when (nextAddr < endAddr) $ do
        getNextEvents;
        execMCOnlyEvents endAddr
  |  e :: _ => do -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: done at " ++ repr e);
                  pure ()

/- Get the next MC event that could interact with LLVM. -/
def popMCEvent : BlockVCG Event := do
  let endAddr ← BlockVCGContext.mcBlockEndAddr <$> read;
  execMCOnlyEvents endAddr;
  let evts ← BlockVCGState.mcEvents <$> get;
  match evts with
  | [] => localBlockError BlockErrorTag.mcEarlyEnvOfBlock ""
  | fst::rst => do
    modify (λ s => {s with mcEvents := rst});
    pure fst


end


-- -- | Move to end of current block.
def mcExecuteToEnd : BlockVCG Unit := do
  let endAddr <- (fun (s : BlockVCGContext) => s.mcBlockEndAddr) <$> read;
  execMCOnlyEvents endAddr;
  let evts <- (fun (s : BlockVCGState) => s.mcEvents) <$> get;
  match evts with
  | [] => pure ()
  | e :: _ => BlockVCG.localBlockError BlockErrorTag.mcEarlyEnvOfBlock (reprStr e)

--------------------------------------------------------------------------------
-- Literal constructors

def mkInt {w : Nat} (v : Int) (H : w > 0) : Smt.Term (SmtSort.bitvec w) := Smt.bvimm' w v

section
open LLVM.Value

structure SortedTerm (lty : LLVMType) : Type :=
  (sort : SmtSort)
  (pf   : lty.toSmtSort? = some sort)
  (term : Smt.Term sort)

def primEval' (s : SmtSort) : Value -> BlockVCG (Smt.Term s)
| ident i => lookupIdent i s
| undef   => freshSymbol "undef" s
| integer i => match s with
  | SmtSort.bitvec w => Smt.bvimm' w i
  | _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort ("Expected a bitvec, got: " ++ s.toString)   
| v => BlockVCG.localBlockError BlockErrorTag.unimplementedFeature ("primEval for " ++ s.toString ++ " at " ++ ppLLVM v)

def primEval (lty : LLVMType) (v : Value) : BlockVCG (SortedTerm lty) :=
  match H: lty.toSmtSort? with
  | none   => BlockVCG.localBlockError BlockErrorTag.unexpectedSort ("Type has no SMT repr: " ++ ppLLVM lty)
  | some s => SortedTerm.mk s H <$> primEval' s v

def primEvalTypedValueAsBV64 (tyVal:Typed Value) : BlockVCG (Smt.Term SmtSort.bv64) := do
  let ⟨s, _, tm⟩ <- primEval tyVal.type tyVal.value
  match s, tm with
  | SmtSort.bitvec 64, tm' => pure tm'
  | _, _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort 
                                     ("expected 64-bit bitvector, got " ++ (ppLLVM tyVal.type))

end


--------------------------------------------------------------------------------
-- Function calls

-- In initial state
def stackHighTerm : BlockVCG x86.vcg.memaddr := do
  let stdLib <- BlockVCGContext.mcStdLib <$> read;
  pure (stdLib.funStartRegs.get_reg64 x86.reg64.rsp)

-- In initial state
def returnAddrTerm : BlockVCG x86.vcg.memaddr := do
  let stdLib <- BlockVCGContext.mcStdLib <$> read;
  -- FIXME
  let sht <- stackHighTerm;
  let addrOp := stdLib.memOps WordSize.word64;
  pure (addrOp.readMem stdLib.blockStartMem sht)

section

open x86.vcg (Event)
open x86.vcg.Event
open BlockVCG (fatalBlockError localBlockError localThrow fatalThrow)


-- | Returns ABI byte alignment constraint in bytes.
def memTypeAlignAux (tyMap : LLVMTypeMap) (orig : LLVMType) : Nat → LLVMType → Std.HashSet String → BlockVCG Nat
| Nat.zero, _, _ =>
  localBlockError BlockErrorTag.outOfFuel ("resolving LLVM type " ++ (ppLLVM orig))
| _, (LLVM.LLVMType.prim pt), _ =>
  match pt with
  | LLVM.PrimType.integer 1 => pure 1 -- FIXME should we pull these from a `DataLayout.integerInfo` somewhere?
  | LLVM.PrimType.integer 8  => pure 1
  | LLVM.PrimType.integer 16 => pure 2
  | LLVM.PrimType.integer 32 => pure 4
  | LLVM.PrimType.integer 64 => pure 8
  | _ => localBlockError BlockErrorTag.unimplementedFeature 
                         ("Alignment of primitive LLVM type " ++ (ppLLVM pt) ++ " is not set.")
| fuel+1, LLVM.LLVMType.alias nm, seen =>
  if seen.contains nm
  then localBlockError BlockErrorTag.aliasCycleDetected ("original type " ++ (ppLLVM orig)) 
  else 
    (match tyMap.find? nm with
     | none => 
       localBlockError BlockErrorTag.llvmTypeNotFound nm
     | some none => 
       localBlockError BlockErrorTag.llvmTypeNotBound nm
     | some (some t) => 
       memTypeAlignAux tyMap orig fuel t (seen.insert nm))
| _, t, _ =>
  localBlockError BlockErrorTag.unimplementedFeature ("alignment of " ++ (ppLLVM t) ++ "not set")

-- | Returns ABI byte alignment constraint in bytes.
def memTypeAlign (tyMap : LLVMTypeMap) (t : LLVMType) : BlockVCG Nat :=
  let fuel : Nat := 1000;
  memTypeAlignAux tyMap t fuel t Std.HashSet.empty

-- | Returns ABI byte alignment constraint in bytes of the type this pointer
-- type points to (or an error if the type is not a pointer type).
def memPtrTypeAlign (tyMap : LLVMTypeMap) : LLVMType → BlockVCG Nat
| LLVM.LLVMType.ptr t => memTypeAlign tyMap t
| t => localBlockError BlockErrorTag.unexpectedSort ("expected an LLVM pointer type, but got " ++ (ppLLVM t))

def llvmLoad (ident : LLVM.Ident) (addr:Typed Value) (mAlign:Option Nat) : BlockVCG Unit := do
  -- Calculate the address
  let llvmAddr ← primEvalTypedValueAsBV64 addr;
  -- Calculate the alignment
  let llvmAlign ← (do
    let a0 : Nat := mAlign.getD 0;
    if a0 == 0 then do
      let typeMap ← (ModuleVCGContext.moduleTypeMap ∘ BlockVCGContext.mcModuleVCGContext) <$> read;
      memPtrTypeAlign typeMap addr.type
    else if ((Nat.land (a0 - 1) a0) ≠ 0)
    then localBlockError BlockErrorTag.invalidAlignment (reprStr a0)
    else pure a0);
  when (llvmAlign > 1) $
    BlockVCG.logWarning $ "LLVM alignment of " ++ (toString llvmAlign) ++ "  is unchecked.";
  -- Get the next machine code event.
  let mevt ← popMCEvent;
  -- Inspect the event
  match mevt with
  | JointStackReadEvent mcAddr readWidth readValVar allocName => do
    -- Check LLVM type and machine code types are equivalent.
    -- EXCEPT we don't have an mcType in the Lean version =\ FIXME...?
    -- perhaps just add a note as to what we're doing instead?
    -- unless (typeCompat llvmType mcType) $ do
    --     fatalBlockError "Incompatible LLVM and machine code types."
    let sz : Smt.Term SmtSort.bv64 := Smt.bvimm 64 readWidth;
    -- Check alloca is defined
    let llvmAllocaMap ← BlockVCGState.activeAllocaMap <$> get;
    let mcAllocaMap ← (x86.vcg.MCStdLib.allocaMap ∘ BlockVCGContext.mcStdLib) <$> read;
    match llvmAllocaMap.find? allocName, mcAllocaMap.find? allocName with
    | none, none =>
      localBlockError BlockErrorTag.unknownAlloc allocName.name
    | none, _ =>
      localBlockError BlockErrorTag.unknownAlloc (allocName.name ++ ", missing LLVM entry") 
    | _, none =>
      localBlockError BlockErrorTag.unknownAlloc (allocName.name ++ ", missing MC entry")
    | some llvm, some mc => do
      -- Prove: LLVM address is in allocation
      proveTrue GoalTag.llvmWriteTargetsAlloc allocName.name (llvm.isInAlloca llvmAddr sz)
      -- Prove: machine code addres is in allocation.
      proveTrue GoalTag.mcWriteTargetsAlloc allocName.name (mc.isInAlloca mcAddr sz)
      -- Assert machine code address is same offset of machine code region as LLVM address.
      let llvmOffset : Smt.Term SmtSort.bv64 :=
        Smt.bvsub llvmAddr llvm.baseAddress;
      let mcOffset : Smt.Term SmtSort.bv64 :=
        Smt.bvsub mcAddr mc.baseAddress;
      proveEq GoalTag.llvmAndMCReadOffsetsMatch "" llvmOffset mcOffset
      -- Define value from reading Macaw heap
      -- supType ← getSupportedType mcType;
      let mcVal ← mcRead mcAddr (SmtSort.bitvec readWidth);
      -- FIXME ^ We skipped this why do we do this... seems redundant,
      -- why not just define _one_ and not both? Are we relying on the non-local usage of
      -- macawValVar somewhere else in the code base and we need to make sure to define it
      -- here... even though we don't pass it anywhere? =(
  
      -- assert that the term from the read event in fact is equal to the memory read result
      addAssert (Smt.eq readValVar mcVal);
      --   defineVarFromReadMCMem macawValVar mcAddr supType
  
      --   -- Define LLVM value in terms of Macaw value.
      let _ <- defineTerm ident mcVal;
      --   addCommand $ SMT.defineFun (identVar ident) [] (supportedSort supType) (varTerm macawValVar)
      pure ()
  | NonStackReadEvent mcAddr readWidth readValVar => do
      -- Check LLVM type and machine code types are equivalent.
      --   unless (typeCompat llvmType mcType) $ do
      --     fatalBlockError "Incompatible LLVM and machine code types."
      -- Assert addresses are the same
      proveEq GoalTag.llvmAndMCLoadAddrsMatch "" mcAddr llvmAddr
      -- Add that macaw points to the heap
      let mcCurAddr ← BlockVCGState.mcCurAddr <$> get;
      let notInStack ← (x86.vcg.MCStdLib.notInStack ∘ BlockVCGContext.mcStdLib) <$> read;
      let sz : Smt.Term SmtSort.bv64 := Smt.bvimm 64 readWidth;
      proveTrue GoalTag.nonStackReadAddrValid "" (notInStack mcAddr sz)
      --   -- Define value from reading Macaw heap
      --   supType <- getSupportedType mcType
      --   defineVarFromReadMCMem macawValVar mcAddr supType
      let mcVal ← mcRead mcAddr (SmtSort.bitvec readWidth);
      addAssert (Smt.eq readValVar mcVal);
      -- Define LLVM value returned in terms of macaw value
      --   addCommand $ SMT.defineFun (identVar ident) [] (supportedSort supType) (varTerm macawValVar)
      let _ <- defineTerm ident mcVal;
      pure ()
  | _ => localBlockError BlockErrorTag.unexpectedEvent "expected a machine code load"
  

def llvmStore (llvmAddr : Smt.Term SmtSort.bv64) {s : SmtSort} (llvmVal : Smt.Term s) : BlockVCG Unit := do
  let mevt ← popMCEvent;
  match mevt with
  | JointStackWriteEvent mcAddr mcValWidth mcVal allocName => do
  --   -- Check the number of bytes written are the same.
  --   unless (typeCompat llvmType mcType) $ do
  --     fatalBlockError $ "Machine code and LLVM writes have incompatible types:\n"
  --         ++ "MC type:   " ++ show mcType ++ "\n"
  --         ++ "LLVM type: " ++ show llvmType

  --   let llvmAllocaBase :: SMT.Term
  --       llvmAllocaBase = varTerm ("llvm_" <> Ann.allocaNameText allocName)
  --   let mcAllocaBase :: SMT.Term
  --       mcAllocaBase = varTerm (allocaMCBaseVar allocName)
  --   -- Steps:
  --   let sz = memReprBytes mcType
  --   -- Prove: machine code addres is valid.
  --   proveTrue (evalRangeCheck (isInMCAlloca allocName) mcAddr sz)
  --             (printf "Check machine code write is in %s alloca." (show allocName))
  --   -- Prove: llvmAddr - llvmAllocaBase = mcAddr - mcAllocaBase
  --   let llvmOffset = SMT.bvsub llvmAddr llvmAllocaBase
  --   let mcOffset   = SMT.bvsub   mcAddr   mcAllocaBase
  --   proveEq llvmOffset mcOffset "LLVM and machine code write to same allocation offset."
  --   -- Assert values are equal
  --   thisIP <- gets mcCurAddr
  --   proveEq llvmVal mcVal $
  --     (printf "Value written at addr %s equals LLVM value." (show thisIP))
    localBlockError BlockErrorTag.unimplementedFeature "llvmStore JointStackWriteEvent"
  | NonStackWriteEvent mcAddr mcValWidth mcVal => do
    proveEq GoalTag.llvmAndMCStoreAddrsMatch "" llvmAddr mcAddr
    let s' : SmtSort := SmtSort.bitvec mcValWidth;
    if hEq : s' = s
    then do
      -- Assert values are equal
      proveEq GoalTag.llvmAndMCStoreEq "" llvmVal (cast (congrArg Smt.Term hEq) mcVal)
    else do
      localBlockError BlockErrorTag.unexpectedSort 
                      ("Machine code writes "++(toString $ toSExpr s')
                       ++" while LLVM writes "++(toString $ toSExpr s))
  | _ => localBlockError BlockErrorTag.unexpectedEvent "llvmStore: expected a heap or joint stack write"

end

def checkDirectionFlagClear (context : String) : BlockVCG Unit := do
  let regs <- BlockVCGState.mcCurRegs <$> get
  let dfVal := regs.get_flag x86.flag.df.index
  proveTrue GoalTag.expectedDirectionFlagVal context (Smt.not dfVal)

def proveLLVMReturn (rv : Typed Value) : BlockVCG Unit := do
  let regs <- BlockVCGState.mcCurRegs <$> get
  let prove (lty : LLVMType) (s : SmtSort) (H : lty.toSmtSort? = some s) 
            (v : Value) 
            (rv : x86.vcg.RegState -> Smt.Term s)
            : BlockVCG Unit := do
      let vv  <- primEval' s v
      proveEq GoalTag.llvmAndMCReturnValuesEq (ppLLVM v) vv (rv regs)

  discard $ forReturnVal (localBlockError BlockErrorTag.unexpectedSort) prove rv

def llvmReturn (mlret : Option (Typed Value)) : BlockVCG Unit := do
  mcExecuteToEnd;
  let regs <- BlockVCGState.mcCurRegs <$> get;
  do let sht  <- stackHighTerm;
     proveEq GoalTag.stackHeightPreserved "after return" (regs.get_reg64 x86.reg64.rsp) (Smt.bvadd sht (Smt.bvimm _ 8))
  do let ra <- returnAddrTerm;
     proveEq GoalTag.returnAddressPreserved "after return" regs.ip ra
  
  checkDirectionFlagClear "function return"

  let stdLib ← BlockVCGContext.mcStdLib <$> read;
  let rEq := λ r => proveEq GoalTag.registerPreserved (r.name ++ ", after return") (regs.get_reg64 r) (stdLib.funStartRegs.get_reg64 r)
  x86CalleeSavedGPRegs.forM rEq;
  match mlret with
  | none => pure ()
  | some v => proveLLVMReturn v

section
open mc_semantics.type

-- c.f. parseLLVMArgs
def checkLLVMArgs (args : List (Typed Value)) : BlockVCG Unit := do
  let regs <- BlockVCGState.mcCurRegs <$> get
  let prove (lty : LLVMType) (s : SmtSort) (H : lty.toSmtSort? = some s) 
            (v : Value) 
            (rv : x86.vcg.RegState -> Smt.Term s)
            : BlockVCG Unit := do
      let vv  <- primEval' s v
      proveEq GoalTag.argAndRegEq (ppLLVM v) vv (rv regs)

  discard $ forEachArg (localBlockError BlockErrorTag.llvmInvokeArgError) prove args
end


def assignLLVMReturn (newRegs : x86.vcg.RegState) (ri : Typed LLVM.Ident) : BlockVCG Unit := do
  let prove (lty : LLVMType) (s : SmtSort) (H : lty.toSmtSort? = some s) 
            (i : LLVM.Ident) 
            (rv : x86.vcg.RegState -> Smt.Term s)
            : BlockVCG Unit :=
      discard $ defineTerm i (rv newRegs);

  discard $ forReturnVal (localBlockError BlockErrorTag.unexpectedSort) prove ri

def llvmInvoke (isTailCall : Bool) (fsym : LLVM.Symbol) (args : Array (Typed Value))
    (lRet : Option (Typed LLVM.Ident)) : BlockVCG Unit := do
  when isTailCall $ localBlockError BlockErrorTag.unimplementedFeature "tail call"

  BlockVCGContext.mcBlockEndAddr <$> read >>= execMCOnlyEvents;

  let regs <- BlockVCGState.mcCurRegs <$> get;

  --------------------
  -- Pre call

  -- FIXME assertFnNameEq fsym regs.ip
  checkLLVMArgs args.toList
  checkDirectionFlagClear "function call"

  let postCallRIP  <- mcNextAddr <$> get;

  -- FIXME: generalise returnAddrTerm?
  -- Check stored return value matches next instruction
  do let addrOnStack <- mcRead (regs.get_reg64 x86.reg64.rsp) _
     proveEq GoalTag.returnAddrNextInstr "" addrOnStack (Smt.bvimm 64 postCallRIP)
        
  --------------------
  -- Post call

  -- Add 8 to RSP for post-call value to represent poping the stack pointer.
  let postCallRSP := Smt.bvadd (regs.get_reg64 x86.reg64.rsp) (Smt.bvimm _ 8);
  -- Create registers (newRegs) for instruction after call.
  --
  -- This ensures that callee saved registers and the stack pointer
  -- are preserved, but nothing is assumed about other registers.
  let newRegs ← do
    let mut regs' ← BlockVCG.runSmtM $
      -- declare fresh constants for all registers and initializes RIP
      x86.vcg.RegState.declare_const ("a" ++ postCallRIP.ppHex  ++ "_")  (ip := postCallRIP) (df := false)
    -- restore callee saved register values
    for r in x86CalleeSavedGPRegs do
      regs' := regs'.set_reg64 r (regs.get_reg64 r)
    -- set expected rsp (x87top is not currently reasoned about)
    regs' := regs'.set_reg64 x86.reg64.rsp postCallRSP
    -- regs' := regs.set_flag X87_TopReg (bvdecimal 7 3)
    pure $ regs'

  modify $ fun s => {s with mcCurRegs := newRegs };

  -- Update machine code memory to post-call memory.
  (do let newMem <- declareMem;
      let oldMem <- BlockVCGState.mcCurMem <$> get;
      let sht    <- stackHighTerm;
      addAssert $ @Smt.eqrange (RangeSort.bitvec 64) _ newMem oldMem postCallRSP (Smt.bvadd sht (Smt.bvimm _ 7));
      modify $ fun s => {s with mcCurMem := newMem });

  -- Assign returned value by assigning LLVM variable
  match lRet with
  | none => pure ()
  | some ri => assignLLVMReturn newRegs ri

--------------------------------------------------------------------------------
-- Arithmetic

section
open LLVM.Value
open LLVM.ICmpOp

def arithOpFunc {n : Nat} : LLVM.ArithOp
                          -> Smt.Term (SmtSort.bitvec n)
                          -> Smt.Term (SmtSort.bitvec n)
                          -> Option (Smt.Term (SmtSort.bitvec n))
| LLVM.ArithOp.add _ _, x, y => Option.some (Smt.bvadd x y) 
| LLVM.ArithOp.sub _ _, x, y => Option.some (Smt.bvsub x y) 
| LLVM.ArithOp.mul _ _, x, y => Option.some (Smt.bvmul x y) 
| _, _, _ => none -- FIXME


-- we don't implement the usw ssw or exact flags
def bitOpFunc {n : Nat} : LLVM.BitOp
                        -> Smt.Term (SmtSort.bitvec n)
                        -> Smt.Term (SmtSort.bitvec n)
                        -> Option (Smt.Term (SmtSort.bitvec n))
| LLVM.BitOp.shl false false, x, y => Option.some (Smt.bvshl x y)
| LLVM.BitOp.lshr false, x, y => Option.some (Smt.bvlshr x y)
| LLVM.BitOp.ashr false, x, y => Option.some (Smt.bvashr x y)
| LLVM.BitOp.and, x, y => Option.some (Smt.bvand x y)
| LLVM.BitOp.or, x, y  => Option.some (Smt.bvor x y )
| LLVM.BitOp.xor, x, y => Option.some (Smt.bvxor x y)
| _, _, _ => Option.none -- FIXME

def icmpOpFunc {n : Nat} : LLVM.ICmpOp
                         -> Smt.Term (SmtSort.bitvec n)
                         -> Smt.Term (SmtSort.bitvec n)
                         -> Smt.Term SmtSort.bool
| ieq, x, y  => Smt.eq x y
| ine, x, y  => Smt.not (Smt.eq x y)
| iugt, x, y => Smt.bvugt x y
| iuge, x, y => Smt.bvuge x y 
| iult, x, y => Smt.bvult x y 
| iule, x, y => Smt.bvule x y 
| isgt, x, y => Smt.bvsgt x y 
| isge, x, y => Smt.bvsge x y 
| islt, x, y => Smt.bvslt x y 
| isle, x, y => Smt.bvsle x y 

end

--------------------------------------------------------------------------------
-- Conversion

section
open LLVM (PrimType)
open LLVM.Value
open LLVM.ConvOp
open LLVM.LLVMType

-- FIXME: this implues we could have constructed an ill-formed term?
def bvSortedTerm {n : Nat} (tm : Smt.Term (SmtSort.bitvec n)) : 
                 Option (SortedTerm (prim (LLVM.PrimType.integer n))) :=
 if H : n > 0 then some (SortedTerm.mk _ (bitvec_toSmtSort? H) tm) else none


theorem some_inj {t : Type} {x y : t} (h : some x = some y) : x = y := by injection h; assumption

def convOpFunc (stdLib : x86.vcg.MCStdLib) : forall (fromTy toTy : LLVMType) {s : SmtSort} 
   (H : fromTy.toSmtSort? = some s),
   LLVM.ConvOp ->
   Smt.Term s  -> 
   Option (SortedTerm toTy)
| _, prim (LLVM.PrimType.integer m), SmtSort.bitvec n, _, trunc, l => do 
  if Hmn : m <= n -- FIXME: we should move these out of VCGBackend
  then bvSortedTerm (x86.vcg.bitvec.trunc m Hmn l)
  else none
| _, prim (LLVM.PrimType.integer m), SmtSort.bitvec n, _, zext, l => 
  bvSortedTerm (x86.vcg.bitvec.uresize n m l)
| _, prim (LLVM.PrimType.integer m), SmtSort.bitvec n, _, sext, l => 
  bvSortedTerm (x86.vcg.bitvec.sresize n m l)
| _, ptr fty, SmtSort.bitvec 64, _, int_to_ptr, l => 
  some (@SortedTerm.mk (ptr fty) _ rfl l)
| _, prim (LLVM.PrimType.integer 64), SmtSort.bitvec 64, _, ptr_to_int, l => 
  some (SortedTerm.mk _ (bitvec_toSmtSort? rfl) l)

| LLVM.LLVMType.vector 8 (prim (LLVM.PrimType.floatType LLVM.FloatType.double))
, prim (LLVM.PrimType.integer 512), _, rfl, bit_cast, l => 
  -- FIXME: generalise
  let ix (n : Nat) (pf : n < 8) := @NTuple.index n (List.replicate 8 (SmtSort.bitvec 64)) pf l
  let tm := x86.vcg.bitvec.concat_list [ ix 7 rfl, ix 6 rfl, ix 5 rfl, ix 4 rfl
                                       , ix 3 rfl, ix 2 rfl, ix 1 rfl, ix 0 rfl]
  some (SortedTerm.mk _ (bitvec_toSmtSort? rfl) tm) 
| prim (LLVM.PrimType.integer 512)
, LLVM.LLVMType.vector 8 (prim (LLVM.PrimType.floatType LLVM.FloatType.double))
, _, rfl, bit_cast, l => 
  -- FIXME: generalise
  let tm : Smt.Term (NTuple.make (List.replicate 8 (SmtSort.bitvec 64))) := 
    LLVM.LLVMType.unpackVecWord 64 rfl 7 l
  some (SortedTerm.mk _ rfl tm)

| prim (LLVM.PrimType.floatType LLVM.FloatType.float)
, prim (LLVM.PrimType.integer 32), _, rfl, fp_to_si, l => 
  let tm := stdLib.fpOps.fp_convert_to_int mc_semantics.float_class.fp32 true x86.RoundingMode.Truncate l
  some (SortedTerm.mk _ rfl tm)
| prim (LLVM.PrimType.floatType LLVM.FloatType.double)
, prim (LLVM.PrimType.integer 64), _, rfl, fp_to_si, l => 
  let tm := stdLib.fpOps.fp_convert_to_int mc_semantics.float_class.fp64 false x86.RoundingMode.Truncate l
  some (SortedTerm.mk _ rfl tm)
  
  -- FIXME: rounding mode
| prim (LLVM.PrimType.integer 32)
, prim (LLVM.PrimType.floatType LLVM.FloatType.float)
, _, rfl, fp_to_si, l => 
  let tm := stdLib.fpOps.int_convert_to_fp mc_semantics.float_class.fp32 true l
  some (SortedTerm.mk _ rfl tm)

| prim (LLVM.PrimType.integer 64)
, prim (LLVM.PrimType.floatType LLVM.FloatType.double)
, _, rfl, fp_to_si, l => 
  let tm := stdLib.fpOps.int_convert_to_fp mc_semantics.float_class.fp64 false l
  some (SortedTerm.mk _ rfl tm)
  
| _, _, _, _, _, _ => none


--       -- FIXME: rounding mode
--       | SmtSort.bitvec 32, SmtSort.bitvec 32, fp_to_si, l => do
--         let stdLib <- BlockVCGContext.mcStdLib <$> read
--         assignTerm (stdLib.fpOps.fp_convert_to_int fp32 true x86.RoundingMode.Truncate l)
--       | SmtSort.bitvec 64, SmtSort.bitvec 64, fp_to_si, l => do
--         let stdLib <- BlockVCGContext.mcStdLib <$> read
--         assignTerm (stdLib.fpOps.fp_convert_to_int fp64 false x86.RoundingMode.Truncate l)

--       -- FIXME: rounding mode
--       | SmtSort.bitvec 32, SmtSort.bitvec 32, si_to_fp, l => do
--         let stdLib <- BlockVCGContext.mcStdLib <$> read
--         assignTerm (stdLib.fpOps.int_convert_to_fp fp32 true l)
--       | SmtSort.bitvec 64, SmtSort.bitvec 64, si_to_fp, l => do
--         let stdLib <- BlockVCGContext.mcStdLib <$> read
--         assignTerm (stdLib.fpOps.int_convert_to_fp fp64 false l)

--       | _, _, _, _ => unimplemented;
--       pure true


end

--------------------------------------------------------------------------------
-- Block Precondition Verification


namespace BlockVCG

/-- Ensure the initial register values when entering a block are as expected.
    In particular the IP and DF (x87Top currently omitted). C.f. `initBlockRegValues`
    in the original prototype. -/
def checkInitBlockRegValues
  (prefixDescr : String)
  (blockAnn : ReachableBlockAnn)
  -- ^ Message to preface verification comments/messages/etc
  (goalFn : Smt.Term SmtSort.bool → Smt.Term SmtSort.bool) : BlockVCG Unit := do
  let regs ← BlockVCGState.mcCurRegs <$> get
  -- Check the instruction pointer
  let actualIP := regs.ip
  let expectedIP := Smt.bvimm 64 blockAnn.startAddr.toNat
  proveTrue GoalTag.expectedInstrPtrVal prefixDescr (goalFn (Smt.eq actualIP expectedIP))
  -- Check the direction flag
  let actualDF := regs.get_flag x86.flag.df.index
  let expectedDF := if blockAnn.dfFlag then Smt.true else Smt.false
  proveTrue GoalTag.expectedDirectionFlagVal prefixDescr (goalFn (Smt.eq actualDF expectedDF))
  -- Check x87Top value
  --let expectedX87Top : Smt.Term SmtSort.bv64 := Smt.bv 64 blockAnn.startAddr.toNat;
  -- (Some X87_TopReg, Smt.bvdecimal (toInteger (Ann.blockX87Top blockAnn)) 3)
  pure ()

-- cf. `verifyBlockPreconditions`
def verifyPreconditions
(prefixDescr : String)
-- ^ Message to preface verification comments/messages/etc
(goalFn : Smt.Term SmtSort.bool → Smt.Term SmtSort.bool)
-- ^ Function applied to predicates before verification allowing us
-- to conditionally validate some of the preconditions.
(lbl : LLVM.BlockLabel)
-- ^ LLVM label of the block we are jumping to.
: BlockVCG Unit := do
  let blkMap ← BlockVCGContext.funBlkAnnotations <$> read;
  match findBlock blkMap lbl with
  | none =>
    localBlockError BlockErrorTag.missingAnnotations ""
  | some (BlockAnn.unreachable, _) =>
    proveTrue GoalTag.blockUnreachable "" (goalFn Smt.false)
  | some (BlockAnn.reachable tgtBlockAnn, varMap) => do
    let firstLabel ← BlockVCGContext.firstBlockLabel <$> read;
    -- Ensure we're not in the first block
    when (lbl == firstLabel) $ localBlockError BlockErrorTag.invalidLLVMInstr "cannot jump to first label in function"

    -- Check initialial register values (IP, DF, and x87Top)
    checkInitBlockRegValues prefixDescr tgtBlockAnn goalFn
  
    let srcLbl ← BlockVCGContext.currentBlock <$> read;
    -- Resolve terms for SMT variables which can appear in precondition statements.
    let resolvePhiVarVal : LLVM.Ident → (LLVM.LLVMType × BlockLabelValMap) → BlockVCG (Sigma Smt.Term) :=
      λ nm val => let (tp, valMap) := val;
                  match valMap.find? srcLbl with
                  | some v => do let ⟨s, _, v'⟩ <- primEval tp v
                                 pure (Sigma.mk s v')
                  | none => localBlockError BlockErrorTag.llvmVarNoInitVal nm.asString
    let phiTermMap ← varMap.mapM resolvePhiVarVal;
    -- Verify each precondition
    for precondExpr in tgtBlockAnn.preconds do
      let p ← evalPrecondition phiTermMap.find? precondExpr
      proveTrue GoalTag.blockPrecondition (precondExpr.toString++", for "++prefixDescr) (goalFn p)

    -- Check allocations are preserved. -- FIXME actually do this when we get to reasoning about allocas.
    -- curAllocas <- gets mcPendingAllocaOffsetMap
    -- when (Ann.blockAllocas tgtBlockAnn /= curAllocas) $ do
    --   localBlockError $ printf "Allocations in jump to %s do not match." (ppBlock lbl)


end BlockVCG



--------------------------------------------------------------------------------
-- stepNextStmt

section
open LLVM.Instruction
open BlockVCG (verifyPreconditions)
open mc_semantics.float_class
open LLVM.LLVMType
    
-- FIXME: move
axiom get_replicate { α : Type } (x : α) : forall (n m : Nat) 
      (pf : m < List.length (List.replicate n x)), -- not m < n to aid in unification
      (List.replicate n x).get m pf = x


section
open List (nil cons)

axiom invert_mapM_Option_cons {α β : Type} {f : α -> Option β} {x : α} {xs : List α}  :
  forall {ys : List β} (pf : List.mapM f (x :: xs) = some ys),
  ∃ y ys', ys = y :: ys' ∧ f x = some y ∧ List.mapM f xs = some ys'--  := by
  -- induction xs with
  -- | nil => intros pf; simp at pf
  -- | cons y ys' ih => intros pf


-- FIXME: move
axiom mapM_Option_length {α β : Type} {f : α -> Option β} {xs : List α} :
  forall  {ys : List β} (pf : List.mapM f xs = some ys),
  ys.length = xs.length -- := by
  -- induction xs with 
  -- | nil => intros pf; injection pf with H; rw <- H; exact rfl
  -- | cons x xs' ih => intros pf; injection pf with H

end  

def insertValue : forall (lty : LLVM.LLVMType) (s s' : SmtSort) (pf : lty.toSmtSort? = some s) 
                  (tm : Smt.Term s) (elt : Smt.Term s') (ns : List Nat), BlockVCG (Smt.Term s)
| _, _, _, _, tm, _, [] => pure tm -- shouldn't happen, maybe we should check?
| vector n ty, s, s', pf, tm, elt, [n'] => 
  -- s is 'NTuple.make (List.replicate n s)', with n > 0 and prim_toSmtSort? ty = some s
  let ⟨s'', H⟩ := LLVM.LLVMType.invert_vector_toSmtSort? pf
  if Hn : n' < n
  then if Hs' : s' = s''
       then let Hn' : n' < List.length (List.replicate n s'') :=
                  cast (congrArg _ (List.lengthReplicateEq n s'').symm) Hn;
            let pf : s' = (List.replicate n s'').get n' Hn' :=
                Eq.trans Hs' (get_replicate s'' _ _ Hn').symm;
            let f := fun _old => ((), cast (congrArg _ pf) elt);
            let tm' : Smt.Term (NTuple.make (List.replicate n s'')) := 
                (NTuple.lens n' Hn' f (cast (congrArg _ H.right) tm)).snd
            pure (cast (congrArg _ H.right).symm tm')

       else localBlockError BlockErrorTag.unexpectedSort ("Expecting " ++ toString s'' ++ " got " ++ toString s')
                       
  else localBlockError BlockErrorTag.unimplementedFeature ("Index out of range")

| struct _ tys, s, s', pf, tm, elt, [n] => 
  let ⟨ss, H⟩ := LLVM.LLVMType.invert_struct_toSmtSort? pf
  if Hn : n < ss.length
  then if Hs' : s' = ss.get n Hn 
       then let f := fun _old => ((), cast (congrArg _ Hs') elt);
            let tm' : Smt.Term (NTuple.make ss) := 
              (NTuple.lens n Hn f (cast (congrArg _ H.right) tm)).snd
            pure (cast (congrArg _ H.right).symm tm')
       else localBlockError BlockErrorTag.unexpectedSort ("Expecting " ++ toString (ss.get n Hn) ++ " got " ++ toString s')
  else localBlockError BlockErrorTag.unimplementedFeature ("Index out of range")

| lty, _, _, _, _, _, _ => localBlockError BlockErrorTag.unimplementedFeature ("Unimplemented insert into " ++ ppLLVM lty)

def stepNextStmt (stmt : LLVM.Stmt) : BlockVCG Bool := do
  let unimplemented {t : Type} : BlockVCG t :=
    BlockVCG.localBlockError BlockErrorTag.unimplementedFeature ("stepNextStmt, " ++ ppLLVM stmt)
  let assignTerm {s : SmtSort} (tm : Smt.Term s) : BlockVCG Unit :=
    (match stmt.assign with
     | none => pure ()
     | some i => do discard $ defineTerm i tm; pure ());
  let assignOptionTerm {s : SmtSort} (tm : Option (Smt.Term s)) : BlockVCG Unit :=
    match tm with
    | none     => unimplemented
    | some tm' => assignTerm tm';
  match stmt.instr with
  | phi _ _ => localBlockError BlockErrorTag.unexpectedPhiVar "stepNextStmt"
--   | alloca : LLVMType -> Option (typed value) -> Option Nat -> instruction

  | arith aop { type := lty, value := lhs } rhs => do
    let ⟨s, _, lhsv⟩ <- primEval lty lhs;
    let rhsv <- primEval' s rhs;
    match s, lhsv, rhsv with
      | SmtSort.bitvec n, l, r => assignOptionTerm (arithOpFunc aop l r) -- option as some are unimplemented
      | _, _, _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort "arithmetic op in stepNextStmt"
    pure true

  | bit bop { type := lty, value := lhs } rhs => do
    let ⟨s, _, lhsv⟩ <- primEval lty lhs;
    let rhsv <- primEval' s rhs;
    match s, lhsv, rhsv with
    | SmtSort.bitvec n, l, r => assignOptionTerm (bitOpFunc bop l r)
    | _, _, _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort "bit in stepNextStmt"
    pure true

  | call tailcall o_ty f args => do
    match f with 
    | LLVM.Value.symbol s =>
      llvmInvoke tailcall s args (match o_ty, stmt.assign with 
                                  | some ty, some i => some ⟨ty, i⟩
                                  | _, _ => none)
    | _ => localBlockError BlockErrorTag.unimplementedFeature "indirect function call"
    pure true

  | icmp bop { type := lty, value := lhs } rhs => do
    let ⟨s, _, lhsv⟩ <- primEval lty lhs;
    let rhsv         <- primEval' s rhs; 
    match s, lhsv, rhsv with
    | SmtSort.bitvec n, l, r => assignTerm (Smt.smtIte (icmpOpFunc bop l r) (Smt.bvimm 1 1) (Smt.bvimm 1 0))
    | _, _, _                => BlockVCG.localBlockError BlockErrorTag.unexpectedSort "icmp in stepNextStmt"
    pure true

    -- match s, stmt.assign, lhsv, rhsv with
    -- | _, none, _, _ => pure ()
    -- | SmtSort.bitvec n, some i, l, r => do 
    --   discard $ defineTerm i (Smt.smtIte (icmpOpFunc bop l r) (Smt.bvimm 1 1) (Smt.bvimm 1 0)); 
    --   pure ()
    -- | _, _, _, _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort "icmp in stepNextStmt"
    -- pure true

  | br { type := _lty, value := cnd } tlbl flbl => do
    mcExecuteToEnd;
    let cndTerm <- primEval' (SmtSort.bitvec 1) cnd;
    let c := Smt.eq cndTerm (Smt.bvimm _ 1);
    verifyPreconditions "true branch"  (Smt.impl c)           tlbl;
    verifyPreconditions "false branch" (Smt.impl (Smt.not c)) flbl;
    pure false
  
  | jump lbl => do
    mcExecuteToEnd;
    verifyPreconditions "jump"  (fun x => x) lbl;
    pure false

  | ret v    => do llvmReturn (some v); pure false
  | retVoid  => do llvmReturn none; pure false

  | conv cop { type := lty, value := lhs } rty => do
    let stdLib <- BlockVCGContext.mcStdLib <$> read
    let ⟨s, H, lv⟩ <- primEval lty lhs
    match convOpFunc stdLib lty rty H cop lv with
    | none => unimplemented
    | some ⟨s', _H', res⟩ => assignTerm res
    pure true

  | load addr mOrd mAlign =>
    if mOrd.isSome then BlockVCG.localBlockError BlockErrorTag.unimplementedFeature "atomic ordering"
    else match stmt.assign with
         | none => BlockVCG.localBlockError BlockErrorTag.llvmInvalidLoad "no assigned identifier"
         | some x => do
           llvmLoad x addr mAlign;
           pure true

  | store (val:Typed Value) (addr:Typed Value) (_align:Option Nat) => do
      let addrTerm ← primEvalTypedValueAsBV64 addr;
      let ⟨_s, _H, valTerm⟩ <- primEval val.type val.value;
      llvmStore addrTerm valTerm;
      pure true

  | select { type := t1, value := e1 } { type := t2, value := e2 } e3 => do
    let ⟨s, _H, v2⟩ <- primEval t2 e2
    match t1, s, v2 with
    | LLVM.LLVMType.prim (LLVM.PrimType.integer 1), SmtSort.bitvec m, v2' => do
      let v1 <- primEval' (SmtSort.bitvec 1) e1
      let v3 <- primEval' (SmtSort.bitvec m) e3
      assignTerm (Smt.smtIte (Smt.eq v1 (Smt.bvimm _ 0)) v3 v2')
    | _, _, _ => BlockVCG.localBlockError BlockErrorTag.unexpectedSort ("select with selty "++(ppLLVM t1))
    pure true

  | insertvalue { type := t1, value := e1 } { type := t2, value := e2 } idxs => do
    let ⟨s1, H, v1⟩  <- primEval t1 e1
    let ⟨s2, _H, v2⟩ <- primEval t2 e2
    let r <- insertValue t1 s1 s2 H v1 v2 idxs.data
    assignTerm r
    pure true

  | _ => unimplemented
  

--   | conv : conv_op -> typed value -> LLVMType -> instruction
--   | alloca : LLVMType -> Option (typed value) -> Option Nat -> instruction
--   | load : typed value -> Option atomic_ordering -> Option Nat /- align -/ -> instruction
--   | store : typed value -> typed value -> Option Nat /- align -/ -> instruction
-- /-
--   | fence : option string -> atomic_ordering -> instruction
--   | cmp_xchg (weak : bool) (volatile : bool) : typed value -> typed value -> typed value
--             -> option string -> atomic_ordering -> atomic_ordering -> instruction
--   | atomic_rw (volatile : bool) : atomic_rw_op -> typed value -> typed value
--             -> option string -> atomic_ordering -> instruction
-- -/
--   | fcmp : fcmp_op -> typed value -> value -> instruction
--   | gep (bounds : Bool) : typed value -> Array (typed value) -> instruction
--   | select : typed value -> typed value -> value -> instruction
--   | extract_value : typed value -> List Nat -> instruction
--   | insert_value : typed value -> typed value -> List Nat -> instruction
--   | extract_elt : typed value -> value -> instruction
--   | insert_elt : typed value -> typed value -> value -> instruction
--   | shuffle_vector : typed value -> value -> typed value -> instruction
--   | invoke : LLVMType -> value -> List (typed value) -> block_label -> block_label -> instruction
--   | comment : String -> instruction
--   | unreachable
--   | unwind
--   | va_arg : typed value -> LLVMType -> instruction
--   | indirect_br : typed value -> List block_label -> instruction
--   | switch : typed value -> block_label -> List (Nat × block_label) -> instruction
--   | landing_pad : LLVMType -> Option (typed value) -> Bool -> List (clause × typed value) -> instruction
--   | resume : typed value -> instruction




--------------------------------------------------------------------------------
-- Alloca Declarations

-- | Add the LLVM declarations for an allocation.
def allocaDeclarations (a : AllocaAnn) : BlockVCG Unit := do
  let nm : LocalIdent := a.ident;
  let sz := a.size;
  -- Get used allocas
  let used ← BlockVCGState.activeAllocaMap <$> get;
  -- Check that alloca name is not in use.
  when (used.contains nm) $ localBlockError BlockErrorTag.allocNameCollision nm.name
  -- Identifies the LLVM base address of an allocation.
  let baseNm : LLVM.Ident := LLVM.Ident.named $ "alloca_" ++ nm.name ++ "_llvm_base";
  -- Identifies the LLVM end address of an allocation.
  let endNm  : LLVM.Ident := LLVM.Ident.named $ "alloca_" ++ nm.name ++ "_llvm_end";
  -- Declare LLVM alloca base and end
  let baseVar ← declareTerm baseNm SmtSort.bv64;
  let endVar ← defineTerm endNm (Smt.bvadd baseVar (Smt.bvimm 64 sz));
  -- Assert alloca end computation did not overflow.
  addAssert $ Smt.bvule baseVar endVar;
  let predNm : String := "llvmaddr_in_alloca_" ++ nm.name;
  -- Introduce predicate to check LLVM addresses.
  let rangeCheck ← BlockVCG.defineRangeCheck predNm baseVar endVar;
  -- Add assumption that LLVM allocation does not overlap with
  -- existing allocations.
  used.forM (λ _ a' => addAssert $ x86.vcg.isDisjoint baseVar endVar a'.baseAddress a'.endAddress);
  -- Define register alloca is returned to.
  let regNm : LLVM.Ident := LLVM.Ident.named $ "llvm_" ++ nm.name;
  let reg ←  defineTerm regNm baseVar;
  -- Add alloca to active set.
  modify (λ s => { s with activeAllocaMap :=
                          used.insert a.ident {baseAddress := baseVar,
                                               endAddress := endVar,
                                               returnRegister := reg,
                                               isInAlloca := rangeCheck}})


end

  
--------------------------------------------------------------------------------
-- Runner

namespace BlockVCG

-- cf. `runBlockVCG`
protected 
def run (mctx : ModuleVCGContext)
        (funAnn : FunctionAnn)
        (bmap : ReachableBlockAnnMap)
        (firstBlock : LLVM.BlockLabel)
        (firstAddr  : MCAddr) -- FIXME: maybe not strictly required
        (thisBlock  : LLVM.BlockLabel)
        (blockAnn   : ReachableBlockAnn)
        (m : BlockVCG Unit) : Except BlockVCGError ((Array VerificationGoal) × (Array VerificationWarning)) := do
  let blockStart := blockAnn.startAddr.toNat;
  let sz := blockAnn.codeSize;
  let blockMap : MCBlockAnnMap :=
    (let mk (e : MCMemoryEvent) := (e.addr.toNat, e.info);
     Std.RBMap.ofList (List.map mk blockAnn.memoryEvents.toList));
  let ((stdLib, blockRegs), (idGen', script)) := Smt.runSmtM IdGen.empty (do
    let ann := mctx.annotations;
    let stdLib <- x86.vcg.MCStdLib.make
                    (ip := firstAddr.addr.toNat)
                    (pageSize := ann.pageSize)
                    (guardPageCount := ann.stackGuardPageCount)
                    (allocas := blockAnn.allocas)
                    (dfFlag := blockAnn.dfFlag)
    let blockRegs <-
      if thisBlock = firstBlock
      then pure stdLib.funStartRegs
      else x86.vcg.RegState.declare_const ("a" ++ blockStart.ppHex ++ "_")  (ip := blockStart) (df := blockAnn.dfFlag)
    pure (stdLib, blockRegs));

  let (eventsF, regsF) := mctx.mkBackendFuns stdLib.fpOps;

  let ctx : BlockVCGContext :=
    { mcModuleVCGContext := mctx
    , llvmFnName := funAnn.llvmFnName
    , funBlkAnnotations := bmap
    , firstBlockLabel := firstBlock
    , currentBlock    := thisBlock
    -- , callbackFns     := prover
    -- ^^ FIXME - upstream code set some settings-related stuff that affected this field
    --            (e.g., are we in interactive or export mode, etc)
    , mcBlockEndAddr  := blockStart + sz
    , mcBlockMap      := blockMap
    , mcStdLib        := stdLib
    , mcInstructionEvents := eventsF
    , mcGetReg          := regsF
    }
  let s : BlockVCGState :=
    { mcCurAddr := blockStart
    , mcCurSize := 0
    , mcCurRegs := blockRegs
    , mcCurMem  := stdLib.blockStartMem
    , mcEvents  := []
    , idGen := idGen' -- passing idGen' twice here probably isn't ideal (i.e., could introduce name collisions via a bug)
    , llvmInstrIndex := 0
    , mcPendingAllocaOffsetMap := blockAnn.allocas
    , activeAllocaMap := Std.RBMap.empty
    , llvmIdentMap  := Std.RBMap.empty
    , smtContext := do set ({revScript := script.reverse, idGen := idGen'} : Smt.SmtState)
    , goals := #[]
    , warnings := #[]
    }
  match (m.run ctx).run s with
  | EStateM.Result.ok _ s' => Except.ok (s'.goals, s'.warnings)
  | EStateM.Result.error e s' => Except.error e

end BlockVCG

-- | Verify c over LLVM stmts
--
-- Note. This is written to take a function rather than directly call
-- @stepNextStmtg@ so that the call stack is cleaner.
def checkEachStmt : List LLVM.Stmt → BlockVCG Unit
| [] => BlockVCG.localBlockError BlockErrorTag.llvmRanOutOfEvents "no block terminator"
| (stmt::stmts) => do
  BlockVCG.addComment $ "LLVM: " ++ (ppLLVM stmt);
  let keepGoing ← stepNextStmt stmt;
  modify (λ s => {s with llvmInstrIndex := s.llvmInstrIndex + 1 });
  if keepGoing then checkEachStmt stmts
  else if stmts.isEmpty then pure ()
  else BlockVCG.localBlockError BlockErrorTag.llvmMissingReturn ""

def defineArgBinding (b : LLVMMCArgBinding) : BlockVCG Unit := do
let funStartRegs ← (x86.vcg.MCStdLib.funStartRegs ∘ BlockVCGContext.mcStdLib) <$> read;
match b.value funStartRegs with
  | Sigma.mk _n v => discard $ defineTerm b.llvmArgName v
pure ()

def definePhiVar (nm : LLVM.Ident) (entry : LLVM.LLVMType × BlockLabelValMap) : BlockVCG Unit := do
let (tp, _) := entry;
match tp.toSmtSort? with
| none   => BlockVCG.localBlockError BlockErrorTag.unexpectedSort ("definePhiVar " ++ ppLLVM tp)
| some s => discard $ declareTerm nm s;

/- Verify a reachable block satisfies its specification. cf `verifyBlock` -/
def verifyReachableBlock
(blockAnn : ReachableBlockAnn)
(args : List LLVMMCArgBinding)
(phiVarMap : PhiVarMap)
(stmts : List LLVM.Stmt)
: BlockVCG Unit := do
  -- Add LLVM declarations for all existing allocations.
  blockAnn.allocas.forM (λ _ a => if a.existing then  allocaDeclarations a else pure ());
  -- Declare LLVM arguments in terms of the registers at function start.
  args.forM defineArgBinding;
  -- Declare phi variables
  phiVarMap.forM definePhiVar;
  let llvmIdentTermMap ← BlockVCGState.llvmIdentMap <$> get;
  -- Assume preconditions
  blockAnn.preconds.forM (λ pExpr => do
                            let pTerm ← evalPrecondition llvmIdentTermMap.find? pExpr;
                            addAssert pTerm);
  -- Start processing LLVM statements
  checkEachStmt stmts


end ReoptVCG
