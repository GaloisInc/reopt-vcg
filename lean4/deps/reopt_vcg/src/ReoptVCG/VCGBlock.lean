
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


namespace ReoptVCG

open LLVM (LLVMType Typed PrimType Value)
open Smt (SmtM SmtSort SmtSort.bool IdGen.empty RangeSort.bitvec)
open x86 (reg64)
open BlockVCG (fatalThrow localThrow)
open x86.vcg (RegState)

namespace BlockVCG


-- | This prepends the LLVM and machine code location information for
-- display to user.
def prependLocation (msg : String) : BlockVCG String := do
fnName ← BlockVCGContext.llvmFunName <$> read;
lbl ← BlockVCGContext.currentBlock <$> read;
instIdx ← BlockVCGState.llvmInstIndex <$> get;
curAddr ← BlockVCGState.mcCurAddr <$> get;
pure $ renderMCInstError fnName lbl instIdx curAddr msg

def addGoal (g : VerificationGoal) : BlockVCG Unit := do
modify (λ s => {s with
                  verificationEvents := (VerificationEvent.goal g) :: s.verificationEvents,
                  goalIndex := s.goalIndex + 1})


-- | Log a message in the timeline of verification events.
def log (msg : String) : BlockVCG Unit := do
locMsg ← prependLocation msg;
let msgEvent := VerificationEvent.msg ⟨locMsg⟩;
modify (λ s => {s with verificationEvents := msgEvent :: s.verificationEvents})


def missingFeature (msg : String) : BlockVCG Unit := do
  log $ "TODO: " ++ msg


-- | Report an error at the given location and stop verification of
-- this block. FIXME this currently uses a callback (which will report an error via IO)
-- _and_ calls `haltBlock`, which will return a local error with an error message. At
-- some point we probably just want to use the latter when we move away from using IO
-- as much.
def fatalBlockError {α} (msg : String) : BlockVCG α := do
errMsg ← prependLocation msg;
fatalThrow errMsg

def localBlockError {α} (msg : String) : BlockVCG α := do
errMsg ← prependLocation msg;
localThrow (BlockError.otherBlockError errMsg)

def addCommand (cmd : Smt.Command) : BlockVCG Unit := do
modify (λ s => {s with smtContext := s.smtContext *> Smt.liftCommand cmd})


def runSmtM {a : Type} (m : SmtM a) : BlockVCG a := do
  let run' := fun (s : BlockVCGState) => 
                  (let r  := Smt.runSmtM s.idGen m;
                       ((r.fst, r.snd.snd.reverse)
                       , {s with idGen := r.snd.fst}));
  (r, cmds) <- modifyGet run';
  _ <- List.mapM addCommand cmds;
  pure r

-- | Add assertion that the propositon is true without requiring it to be proven.
def addAssert (p : Smt.Term SmtSort.bool) : BlockVCG Unit := 
  addCommand $ Smt.Command.assert p

-- | @proveTrue p msg@ adds a proof obligation @p@ is true for all
-- interpretations of constants with the message @msg@.
def proveTrue (prop : Smt.Term SmtSort.bool) (msg : String) : BlockVCG Unit := do
annMsg <- prependLocation msg;
verifyGoal (Smt.not prop) annMsg

def proveFalse (prop : Smt.Term SmtSort.bool) (msg : String) : BlockVCG Unit := do
annMsg <- prependLocation msg;
verifyGoal prop annMsg

def proveEq {s : SmtSort} (x y : Smt.Term s) (msg : String) : BlockVCG Unit := do
annMsg <- prependLocation msg;
proveTrue (Smt.eq x y) annMsg; -- FIXME ? was proveFalseCallback/Smt.distinct
-- Add command for future proofs
addAssert (Smt.eq x y)


-- | Add assertion that the propositon is true without requiring it to be proven.
def addComment (str : String) : BlockVCG Unit :=
  addCommand $ Smt.Command.comment str -- FIXME?


def defineRangeCheck (name : String) (low high : Smt.Term SmtSort.bv64)
  : BlockVCG (Smt.Term SmtSort.bv64 -> Smt.Term SmtSort.bv64 -> Smt.Term SmtSort.bool) :=
runSmtM $ x86.vcg.defineRangeCheck name low high

end BlockVCG

export BlockVCG (addCommand proveTrue proveEq addAssert addComment)

open BlockVCG (localBlockError)

--------------------------------------------------------------------------------
-- Type <-> SMT

@[reducible]
def HasSMTSort : LLVMType -> Prop
| LLVM.LLVMType.ptr _  => True
| LLVM.LLVMType.prim pt  =>
  match pt with
  | LLVM.PrimType.integer i => i > 0
  | _ => False
| _ => False

-- | Convert LLVM type to SMT sort.
def asSMTSort : forall (tp : LLVMType) (pf : HasSMTSort tp), SmtSort
| LLVM.LLVMType.ptr _, _  => SmtSort.bitvec 64
| LLVM.LLVMType.prim (LLVM.PrimType.integer i), _ => SmtSort.bitvec i

namespace HasSMTSort

open LLVM.LLVMType
open LLVM.PrimType

protected 
def dec : forall (tp : LLVMType), Decidable (HasSMTSort tp)
| ptr t  => isTrue True.intro
| prim pt =>
  match pt with 
  | integer i    => Nat.decLt _ _
  | label        => isFalse (fun x => x) 
  | token        => isFalse (fun x => x) 
  | void         => isFalse (fun x => x) 
  | floatType  _ => isFalse (fun x => x)
  | x86mmx       => isFalse (fun x => x) 
  | metadata     => isFalse (fun x => x) 
| alias _        => isFalse (fun x => x)  
| array _ _      => isFalse (fun x => x)  
| funType _ _ _  => isFalse (fun x => x)
| struct _ _     => isFalse (fun x => x)  
| vector _ _     => isFalse (fun x => x)  

instance {tp : LLVMType} : Decidable (HasSMTSort tp) := HasSMTSort.dec tp

end HasSMTSort

def asSMTSort' (tp : LLVMType) : Option SmtSort :=
  if H : HasSMTSort tp then some (asSMTSort tp H) else none

def coerceToSMTSort (ty : LLVMType) : BlockVCG SmtSort :=
  match asSMTSort' ty with
  | some tp => pure tp
  | none    => BlockVCG.fatalBlockError $ "Unexpected type " ++ (ppLLVM ty)

--------------------------------------------------------------------------------
-- Ident <-> SMT

def lookupIdent (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  m <- BlockVCGState.llvmIdentMap <$> get;
  match m.find? i with
  | some (Sigma.mk s' tm) => 
    if H : s' = s then pure (Eq.recOn H tm) else BlockVCG.fatalBlockError ("Sort mismatch for " ++ i.asString)
  | none => BlockVCG.fatalBlockError ("Unknown ident: " ++ i.asString)

def freshIdent (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  sym <- BlockVCG.runSmtM (Smt.freshSymbol i.asString); -- FIXME: this should be primitive in SMT
  let tm := Smt.mkSymbol sym s;
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ tm)});
  pure tm

def defineTerm {s : SmtSort} (i : LLVM.Ident) (tm : Smt.Term s) : BlockVCG (Smt.Term s) := do
  sym <- BlockVCG.runSmtM (Smt.defineFun i.asString [] s tm);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym

def declareTerm (i : LLVM.Ident) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  sym <- BlockVCG.runSmtM (Smt.declareFun i.asString [] s);
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
  ctx <- read;
  s <- get;
  let addr := mcNextAddr s;
  when (not (addr < ctx.mcBlockEndAddr)) $ 
    localBlockError $ "Unexpected end of machine code events.";
  -- FIXMEL df, x87Top
  -- BlockVCG.liftIO $ IO.println ("Decoding at " ++ addr.ppHex);

  addComment ("MC: at " ++ addr.ppHex);

  (events, idGen', sz) <-
    match x86.vcg.instructionEvents ctx.mcBlockMap s.mcCurRegs s.idGen addr
            ctx.mcModuleVCGContext.decoder with
    | Except.error e => localBlockError e
    | Except.ok    r => pure r;

  -- Update local index and next addr
  set $ { s with idGen := idGen'
               , mcCurAddr := addr
               , mcCurSize := sz
               , mcEvents := events
        }



-- | Set machine code registers from reg state.
def setMCRegs (regs : x86.vcg.RegState) : BlockVCG Unit :=
  -- FIXME
  -- topVal <- case regs^.boundValue X87_TopReg of
  --             BVValue _w i | 0 <= i, i <= 7 -> pure $! fromInteger i
  --             _ -> error "Unexpected X87_TOP value"
  -- dfVal <- case regs^.boundValue DF of
  --            BoolValue b -> pure b
  --            _ -> error "Unexpected direction flag"
  modify $ fun s => { s with mcCurRegs := regs }


def getSupportedType (s : SmtSort) : BlockVCG (x86.vcg.SupportedMemType s) := do
  mcstd  <- BlockVCGContext.mcStdLib <$> read;
  let mops := mcstd.memOpsBySort;
  match mops s with
  | some ops => pure ops
  | none => localBlockError $ "Unexpected type " ++ toString s

def declareMem : BlockVCG x86.vcg.memory :=
  BlockVCG.runSmtM $ Smt.declareFun "mem" [] x86.vcg.memory_t

def mcWrite (addr : x86.vcg.memaddr) (s : SmtSort) (val : Smt.Term s) : BlockVCG Unit := do
  curMem <- (fun (s : BlockVCGState) => s.mcCurMem) <$> get;
  supType <- getSupportedType s;
  nextMem <- BlockVCG.runSmtM $ Smt.defineFun "mem" [] x86.vcg.memory_t (supType.writeMem curMem addr val);
  modify $ fun s => { s with mcCurMem := nextMem }

def mcRead (addr : x86.vcg.memaddr) (s : SmtSort) : BlockVCG (Smt.Term s) := do
  curMem <- BlockVCGState.mcCurMem <$> get;
  supType <- getSupportedType s;
  pure (supType.readMem curMem addr)

def mcAssignRead (addr : x86.vcg.memaddr) (s : SmtSort) (smtVar : Smt.Term s) : BlockVCG Unit := do
  v <- mcRead addr s;
  addAssert (Smt.eq smtVar v)

-- | Execute the machine-code only events that occur before jumping to the given address
partial
def execMCOnlyEvents : MemAddr -> BlockVCG Unit
| endAddr => do
  evts <- BlockVCGState.mcEvents <$> get;
  match evts with
  | Command cmd :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: Command");
      addCommand cmd;
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr
  | Warning msg :: mevs => do
      BlockVCG.log msg;
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

      (do thisIP <- BlockVCGState.mcCurAddr <$> get;
          stdLib <- BlockVCGContext.mcStdLib <$> read;
          -- FIXME: assert 8 dvd n
          -- FIMXE: make this take a Nat?
          proveTrue (stdLib.onStack mcAddr (Smt.bvimm _ (n / 8)))
            ("machine code read at " ++ thisIP.ppHex ++ " is not within stack space."));

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

      -- FIXME - once we have allocas this will need to be mcOnlyStackRange
      (do thisIP <- BlockVCGState.mcCurAddr <$> get;
          stdLib <- BlockVCGContext.mcStdLib <$> read;
          -- FIXME: assert 8 dvd n
          proveTrue (stdLib.onStack mcAddr (Smt.bvimm _ (n / 8)))
            ("machine code write at " ++ thisIP.ppHex ++ " is in unreserved stack space."));

      -- do addr <- mcCurAddr <$> get;
      --    proveTrue (evalRangeCheck mcOnlyStackRange mcAddr (memReprBytes tp)) $
      --      printf "machine code write at %s is in unreserved stack space." (show addr)
      -- Update stack with write.
      mcWrite mcAddr (SmtSort.bitvec n) smtVal;
      -- Process next events
      modify $ fun s => {s with mcEvents := mevs };
      execMCOnlyEvents endAddr
    -- This checks to see if the next instruction jumps to the next ip,
    -- and if so it runs it.
  | FetchAndExecuteEvent regs :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: fetch and exec case");
      when (not mevs.isEmpty) $ localBlockError "MC event after fetch and execute";
      modify $ fun s => { s with mcEvents := [] };
      -- Update registers
      setMCRegs regs;
      -- Process next events
      nextAddr <- mcNextAddr <$> get;
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
      nextAddr <- mcNextAddr <$> get;
      when (nextAddr < endAddr) $ do
        getNextEvents;
        execMCOnlyEvents endAddr
  |  e :: _ => do -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: done at " ++ repr e);
                  pure ()

/-- Get the next MC event that could interact with LLVM. --/
def popMCEvent : BlockVCG Event := do
  endAddr ← BlockVCGContext.mcBlockEndAddr <$> read;
  execMCOnlyEvents endAddr;
  evts ← BlockVCGState.mcEvents <$> get;
  match evts with
  | [] => localBlockError "Reached the end of block prematurely."
  | fst::rst => do
    modify (λ s => {s with mcEvents := rst});
    pure fst


end


-- -- | Move to end of current block.
def mcExecuteToEnd : BlockVCG Unit := do
  endAddr <- (fun (s : BlockVCGContext) => s.mcBlockEndAddr) <$> read;
  execMCOnlyEvents endAddr;
  evts <- (fun (s : BlockVCGState) => s.mcEvents) <$> get;
  match evts with
  | [] => pure ()
  | e :: _ => BlockVCG.localBlockError $ "Expecting end of block, got " ++ repr e

--------------------------------------------------------------------------------
-- Literal constructors

def mkInt {w : Nat} (v : Int) (H : w > 0)
  : Smt.Term (asSMTSort (LLVM.LLVMType.prim (LLVM.PrimType.integer w)) H) :=
  Smt.bvimm' w v

section
open LLVM.Value

def primEval : forall (tp : LLVMType) (H :HasSMTSort tp), Value -> BlockVCG (Smt.Term (asSMTSort tp H))
| tp, H, ident i => lookupIdent i (asSMTSort tp H)
| LLVM.LLVMType.prim (LLVM.PrimType.integer w), H, integer i => pure (mkInt i H)
| _, _, _ => BlockVCG.localBlockError "unimplemented"


def primEvalTypedValueAsBV64 (tyVal:Typed Value) : BlockVCG (Smt.Term SmtSort.bv64) :=
if H : HasSMTSort tyVal.type
then do
  v <- primEval tyVal.type H tyVal.value;
  match asSMTSort tyVal.type H, v with
  | SmtSort.bitvec 64, v' => pure v'
  | _, _ => BlockVCG.localBlockError $ "Non 64-bit bitvector sort: " ++ (ppLLVM tyVal.type)
else BlockVCG.localBlockError $ "Non 64-bit bitvector sort: " ++ (ppLLVM tyVal.type)


end

-- --------------------------------------------------------------------------------
-- -- Branch support


-- AMK: `initBlockRegValues` is used in the Haskell implementation of `verifyBlockPreconditions`
--      ... but for ours I just use a helper `checkInitRegVals` since there isn't an obvious
--      analogue to the `X86Reg` from flexdis86 (i.e., a way to index the IP, X87 top reg, and DF)..
-- def initBlockRegValues (ann : ReachableBlockAnn) : List (Fin 16 × Smt.Term (SmtSort.bitvec 64)) :=
--   [ (Some X86_IP,     Smt.bvhexadecimal (toInteger (Ann.blockAddr blockAnn)) 64)
--   -- , (Some X87_TopReg, Smt.bvdecimal (toInteger (Ann.blockX87Top blockAnn)) 3)
--   -- , (Some DF,         if Ann.blockDFFlag blockAnn then Smt.true else Smt.false)
--   ]


--------------------------------------------------------------------------------
-- Function calls

-- In initial state
def stackHighTerm : BlockVCG x86.vcg.memaddr := do
  stdLib <- BlockVCGContext.mcStdLib <$> read;
  pure (stdLib.funStartRegs.get_reg64 x86.reg64.rsp)

-- In initial state
def returnAddrTerm : BlockVCG x86.vcg.memaddr := do
  stdLib <- BlockVCGContext.mcStdLib <$> read;
  -- FIXME
  sht <- stackHighTerm;
  let addrOp := stdLib.memOps WordSize.word64;
  pure (addrOp.readMem stdLib.blockStartMem sht)


axiom VCGBlock_sorry: forall P, P

-- Converts a machine word to be the same width as a given LLVM type.  In the monad to allow failure
def wordAsType (w : x86.vcg.bitvec 64) (ty : LLVMType)
  : BlockVCG (PSigma (fun (H : HasSMTSort ty) => Smt.Term (asSMTSort ty H))) := 
  match ty with 
| ty@(LLVM.LLVMType.ptr _) => do
  let pf : HasSMTSort ty := True.intro;
  pure (PSigma.mk pf w)
| ty@(LLVM.LLVMType.prim (LLVM.PrimType.integer 64)) => do
  let pf : HasSMTSort ty := rfl; -- proves 0 < 64 = true, sort of grossly
  pure (PSigma.mk pf w)
| ty@(LLVM.LLVMType.prim (LLVM.PrimType.integer i)) => do
  if H : 0 < i /\ i < 64                                     
  then do let pf : HasSMTSort ty := H.left;
           let pf' : (i - 1 + 1) - 0 = i := VCGBlock_sorry _;
           let smcv0 := Smt.extract (i - 1) 0 w;
           let r := @Eq.recOn _ _ (fun a _ => Smt.Term (SmtSort.bitvec a)) _ pf' smcv0;
           pure (PSigma.mk pf r)
   else BlockVCG.localBlockError "Unexpected sort in wordAsType"
| _ => BlockVCG.localBlockError "Unexpected sort in wordAsType"
  
def proveRegRel (msg : String) (w : x86.vcg.bitvec 64)
  : LLVM.Typed LLVM.Value ->  BlockVCG Unit
| { type := ty, value := v } => do  
  PSigma.mk pf mcv <- wordAsType w ty;
  lv <- primEval ty pf v;
  proveEq lv mcv msg


section

open x86.vcg (Event)
open x86.vcg.Event
open BlockVCG (fatalBlockError localBlockError localThrow fatalThrow)


-- | Returns ABI byte alignment constraint in bytes.
def memTypeAlignAux (tyMap : LLVMTypeMap) (orig : LLVMType) : Nat → LLVMType → Std.HashSet String → BlockVCG Nat
| Nat.zero, _, _ =>
  localBlockError $ "Ran out of fuel chasing down the definition of type " ++ (ppLLVM orig)
| _, (LLVM.LLVMType.prim pt), _ =>
  (match pt with
   | LLVM.PrimType.integer 16 => pure 2
   | LLVM.PrimType.integer 32 => pure 4
   | LLVM.PrimType.integer 64 => pure 8
   | _ => localBlockError $ "Alignment of primitive LLVM type " ++ (ppLLVM pt) ++ " is not yet set.")
| fuel+1, LLVM.LLVMType.alias nm, seen =>
  if seen.contains nm
  then localBlockError $ "Loop in aliases, starting with " ++ (ppLLVM orig) ++ "." 
  else 
    (match tyMap.find? nm with
     | none => 
       localBlockError $ "Could not find type " ++ nm ++ " in the environment."
     | some none => 
       localBlockError $ "The environment contained " ++ nm ++ " but no associated type."
     | some (some t) => 
       memTypeAlignAux fuel t (seen.insert nm))
| _, t, _ =>
  localBlockError $ "Alignment of " ++ (ppLLVM t) ++ " is not yet set."

-- | Returns ABI byte alignment constraint in bytes.
def memTypeAlign (tyMap : LLVMTypeMap) (t : LLVMType) : BlockVCG Nat :=
let fuel : Nat := 1000;
memTypeAlignAux tyMap t fuel t Std.HashSet.empty

-- | Returns ABI byte alignment constraint in bytes of the type this pointer
-- type points to (or an error if the type is not a pointer type).
def memPtrTypeAlign (tyMap : LLVMTypeMap) : LLVMType → BlockVCG Nat
| LLVM.LLVMType.ptr t => memTypeAlign tyMap t
| t => localBlockError $ "Expected an LLVM pointer type, but got " ++ (ppLLVM t)

def llvmLoad (ident : LLVM.Ident) (addr:Typed Value) (mAlign:Option Nat) : BlockVCG Unit := do
-- Calculate the address
llvmAddr ← primEvalTypedValueAsBV64 addr;
-- Calculate the alignment
llvmAlign ← (do
  let a0 : Nat := mAlign.getD 0;
  if a0 == 0 then do
    typeMap ← (ModuleVCGContext.moduleTypeMap ∘ BlockVCGContext.mcModuleVCGContext) <$> read;
    memPtrTypeAlign typeMap addr.type
  else if ((Nat.land (a0 - 1) a0) ≠ 0)
  then localBlockError $ "Alignment `" ++ (repr a0) ++ "` is not a power of 2."
  else pure a0);
when (llvmAlign > 1) $
  BlockVCG.log $ "Warning: LLVM alignment of " ++ (repr llvmAlign) ++ "  is unchecked.";
-- Get the next machine code event.
mevt ← popMCEvent;
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
  llvmAllocaMap ← BlockVCGState.activeAllocaMap <$> get;
  mcAllocaMap ← (x86.vcg.MCStdLib.allocaMap ∘ BlockVCGContext.mcStdLib) <$> read;
  match llvmAllocaMap.find? allocName, mcAllocaMap.find? allocName with
  | none, none =>
    localBlockError $ "Unknown allocation: " ++ allocName.name
  | none, _ =>
    localBlockError $ "Unknown allocation (missing LLVM entry): " ++ allocName.name
  | _, none =>
    localBlockError $ "Unknown allocation (missing MC entry): " ++ allocName.name
  | some llvm, some mc => do
    -- Prove: LLVM address is in allocation
    proveTrue (llvm.isInAlloca llvmAddr sz) $
      "Check LLVM write address targets " ++ allocName.name ++ " allocation.";
    -- Prove: machine code addres is in allocation.
    proveTrue (mc.isInAlloca mcAddr sz) $
      "Check machine code write address targets " ++ allocName.name ++ " allocation.";
    -- Assert machine code address is same offset of machine code region as LLVM address.
    let llvmOffset : Smt.Term SmtSort.bv64 :=
      Smt.bvsub llvmAddr llvm.baseAddress;
    let mcOffset : Smt.Term SmtSort.bv64 :=
      Smt.bvsub mcAddr mc.baseAddress;
    proveEq llvmOffset mcOffset
      "LLVM and machine code read from same allocation offset.";
    -- Define value from reading Macaw heap
    -- supType ← getSupportedType mcType;
    mcVal ← mcRead mcAddr (SmtSort.bitvec readWidth);
    -- FIXME ^ We skipped this why do we do this... seems redundant,
    -- why not just define _one_ and not both? Are we relying on the non-local usage of
    -- macawValVar somewhere else in the code base and we need to make sure to define it
    -- here... even though we don't pass it anywhere? =(

    -- assert that the term from the read event in fact is equal to the memory read result
    addAssert (Smt.eq readValVar mcVal);
    --   defineVarFromReadMCMem macawValVar mcAddr supType

    --   -- Define LLVM value in terms of Macaw value.
    _ ← defineTerm ident mcVal;
    --   addCommand $ SMT.defineFun (identVar ident) [] (supportedSort supType) (varTerm macawValVar)
    pure ()
| NonStackReadEvent mcAddr readWidth readValVar => do
    -- Check LLVM type and machine code types are equivalent.
    --   unless (typeCompat llvmType mcType) $ do
    --     fatalBlockError "Incompatible LLVM and machine code types."
    -- Assert addresses are the same
    proveEq mcAddr llvmAddr
      "Machine code heap load address matches expected from LLVM";
    -- Add that macaw points to the heap
    mcCurAddr ← BlockVCGState.mcCurAddr <$> get;
    notInStack ← (x86.vcg.MCStdLib.notInStack ∘ BlockVCGContext.mcStdLib) <$> read;
    let sz : Smt.Term SmtSort.bv64 := Smt.bvimm 64 readWidth;
    proveTrue (notInStack mcAddr sz) $
      "Read from heap at " ++ (toString $ toSExpr mcAddr) ++ " is valid.";
    --   -- Define value from reading Macaw heap
    --   supType <- getSupportedType mcType
    --   defineVarFromReadMCMem macawValVar mcAddr supType
    mcVal ← mcRead mcAddr (SmtSort.bitvec readWidth);
    addAssert (Smt.eq readValVar mcVal);
    -- Define LLVM value returned in terms of macaw value
    --   addCommand $ SMT.defineFun (identVar ident) [] (supportedSort supType) (varTerm macawValVar)
    _ ← defineTerm ident mcVal;
    pure ()
| _ => localBlockError "Expected a machine code load event."
  

def llvmStore (llvmAddr : Smt.Term SmtSort.bv64) {s : SmtSort} (llvmVal : Smt.Term s) : BlockVCG Unit := do
  mevt ← popMCEvent;
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
    localBlockError "TODO: implement llvmStore JointStackWriteEvent"
  | NonStackWriteEvent mcAddr mcValWidth mcVal => do
    proveEq llvmAddr mcAddr "Machine code and LLVM heap write addresses are equal";
    let s' : SmtSort := SmtSort.bitvec mcValWidth;
    if hEq : s' = s
    then do
      -- Assert values are equal
      proveEq llvmVal (cast (congrArg Smt.Term hEq) mcVal)
        "Machine code heap store matches expected from LLVM"
    else do
      localBlockError $ "Machine code write has type " ++ (toString $ toSExpr s') ++
                        " while LLVM write has types " ++ (toString $ toSExpr s) ++ "."
  | _ => localBlockError "llvmStore: Expected a heap or joint stack write event."

end

def llvmReturn (mlret : Option (Typed Value)) : BlockVCG Unit := do
  mcExecuteToEnd;
  regs <- BlockVCGState.mcCurRegs <$> get;
  _ <- (do sht  <- stackHighTerm;
           proveEq (regs.get_reg64 x86.reg64.rsp) (Smt.bvadd sht (Smt.bvimm _ 8))
             "stack height at return matches init.");
  _ <- (do ra <- returnAddrTerm;
           proveEq regs.ip ra "return address matches entry value.");
  
  -- FIXME checkDirectionFlagClear
  stdLib <- BlockVCGContext.mcStdLib <$> read;
  let rEq r := proveEq (regs.get_reg64 r) (stdLib.funStartRegs.get_reg64 r)
                  ("value of " ++ r.name ++ " at return is preserved.");
  List.forM rEq x86CalleeSavedGPRegs;
  
  match mlret with
  | none => pure ()
  | some v =>
    proveRegRel "return values match" (regs.get_reg64 x86.reg64.rax) v
  
def llvmInvoke (isTailCall : Bool) (fsym : LLVM.Symbol) (args : Array (Typed Value))
    (lRet : Option (LLVM.Ident × LLVMType)) : BlockVCG Unit := do
  when isTailCall $ localBlockError "Tail calls are unimplemented";

  BlockVCGContext.mcBlockEndAddr <$> read >>= execMCOnlyEvents;

  regs <- BlockVCGState.mcCurRegs <$> get;

  --------------------
  -- Pre call

  -- FIXME assertFnNameEq fsym regs.ip
  when (args.size > x86ArgGPRegs.length) $ 
    localBlockError "Too many arguments";

  let proveOne v (r : x86.reg64) := 
    proveRegRel ("argument matches register " ++ r.repr) (regs.get_reg64 r) v;
  List.forM₂ proveOne args.toList x86ArgGPRegs;

  -- FIXME checkDirectionFlagClear;
  postCallRIP  <- mcNextAddr <$> get;

  -- FIXME: generalise returnAddrTerm?
  -- Check stored return value matches next instruction
  (do addrOnStack <- mcRead (regs.get_reg64 x86.reg64.rsp) _;
      proveEq addrOnStack (Smt.bvimm 64 postCallRIP) "return address matches next instruction.");
        
  --------------------
  -- Post call

  -- Construct new register after the call.
  let postCallRSP := Smt.bvadd (regs.get_reg64 x86.reg64.rsp) (Smt.bvimm _ 8);
  -- create a 
  newRegs <- (do rs <- BlockVCG.runSmtM $ 
                       x86.vcg.RegState.declare_const ("a" ++ postCallRIP.ppHex  ++ "_")  postCallRIP;
                 let rs_with_rsp := x86.vcg.RegState.update_reg64 x86.reg64.rsp (fun _ => postCallRSP) rs;
                 let copy_reg s r := x86.vcg.RegState.update_reg64 r (fun _ => regs.get_reg64 r) s;
                 pure (List.foldl copy_reg rs_with_rsp x86CalleeSavedGPRegs));

  modify $ fun s => {s with mcCurRegs := newRegs };

  -- Update machine code memory to post-call memory.
  (do newMem <- declareMem;
      oldMem <- BlockVCGState.mcCurMem <$> get;
      sht    <- stackHighTerm;
      addAssert $ @Smt.eqrange (RangeSort.bitvec 64) _ newMem oldMem postCallRSP (Smt.bvadd sht (Smt.bvimm _ 7));
      modify $ fun s => {s with mcCurMem := newMem });

  -- Assign returned value by assigning LLVM variable
  match lRet with
  | none => pure ()
  | some (i, ty) => do
    PSigma.mk pf mcv <- wordAsType (newRegs.get_reg64 x86.reg64.rax) ty;
    _ <- defineTerm i mcv;
    pure ()

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

def tryPrimEval (tp : LLVMType) (v:Value) : BlockVCG (Sigma Smt.Term) :=
if h : HasSMTSort tp
then do
  t ← primEval tp h v;
  pure $ ⟨asSMTSort tp h, t⟩
else
  BlockVCG.localBlockError $ "unable to evaluate llvm term "++(ppLLVM v)++" at type "++(ppLLVM tp)


--------------------------------------------------------------------------------
-- Block Precondition Verification


namespace BlockVCG


-- def checkInitRegVals
-- (blockAnn : ReachableBlockAnn)
-- -- ^ Message to preface verification comments/messages/etc
-- (goalFn : Smt.Term SmtSort.bool → Smt.Term SmtSort.bool)
--  : BlockVCG Unit := do
-- -- Check the instruction pointer
-- let expectedIp : Smt.Term SmtSort.bv64 := Smt.bvimm 64 blockAnn.startAddr.toNat;
-- regs <- BlockVCGState.mcCurRegs <$> get;               
-- proveTrue (goalFn (Smt.eq expectedIp regs.ip)) "Checking the IP register.";

-- -- Check x87Top value
-- --let expectedX87Top : Smt.Term SmtSort.bv64 := Smt.bv 64 blockAnn.startAddr.toNat;
-- -- (Some X87_TopReg, Smt.bvdecimal (toInteger (Ann.blockX87Top blockAnn)) 3)
-- -- FIXME check BlockVCGState.mcX87Top value against expected ^
-- -- Check the direction flag
-- --let expectedDF : Smt.Term SmtSort.bv64 := Smt.bvimm 64 blockAnn.startAddr.toNat;
-- -- (Some DF,         if Ann.blockDFFlag blockAnn then Smt.true else Smt.false)
-- -- FIXME check BlockVCGState.mcDF value against expected ^
-- pure ()

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
blkMap ← BlockVCGContext.funBlkAnnotations <$> read;
match findBlock blkMap lbl with
| none =>
  localBlockError $ "Target block "++(ppBlockLabel lbl)++" lacks annotations."
| some (BlockAnn.unreachable, _) =>
  proveTrue (goalFn Smt.false) $ "target block "++(ppBlockLabel lbl)++"is unreachable."
| some (BlockAnn.reachable tgtBlockAnn, varMap) => do
  firstLabel ← BlockVCGContext.firstBlockLabel <$> read;
  -- Ensure we're not in the first block
  when (lbl == firstLabel) $ localBlockError "LLVM should not jump to first label in function.";
  -- Check initialized register values (just rip for now)
  (do regs <- BlockVCGState.mcCurRegs <$> get;
      let expected := Smt.bvimm 64 tgtBlockAnn.startAddr.toNat;
      proveTrue (goalFn (Smt.eq expected regs.ip))
        (prefixDescr ++ " register rip."));

  -- checkInitRegVals tgtBlockAnn goalFn;

  srcLbl <- BlockVCGContext.currentBlock <$> read;
  -- Resolve terms for SMT variables which can appear in precondition statements.
  let resolvePhiVarVal : LLVM.Ident → (LLVM.LLVMType × BlockLabelValMap) → BlockVCG (Sigma Smt.Term) :=
    λ nm val => let (tp, valMap) := val;
                match valMap.find? srcLbl with
                | some v => tryPrimEval tp v
                | none => localBlockError $ "Could not find initial value of llvm variable `"++nm.asString++"`.";
  phiTermMap ← varMap.mapM resolvePhiVarVal;
  -- Verify each precondition
  tgtBlockAnn.preconds.forM (λ precondExpr => do
                               p ← evalPrecondition phiTermMap.find? precondExpr;
                               proveTrue (goalFn p) $ prefixDescr++" precondition: "++precondExpr.toString)
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

def stepNextStmt (stmt : LLVM.Stmt) : BlockVCG Bool := do
  let unimplemented {t : Type} : BlockVCG t :=
    BlockVCG.localBlockError ("(stepNextStmt) Unsupported term" ++ ppLLVM stmt);
  let assignTerm {s : SmtSort} (tm : Smt.Term s) : BlockVCG Unit :=
    (match stmt.assign with
     | none => pure ()
     | some i => do _ <- defineTerm i tm; pure ());
  let assignOptionTerm {s : SmtSort} (tm : Option (Smt.Term s)) : BlockVCG Unit :=
    match tm with
    | none     => unimplemented
    | some tm' => assignTerm tm';
  match stmt.instr with
  | phi _ _ => localBlockError "Unexpected phi in stepNextStmt"
--   | alloca : LLVMType -> Option (typed value) -> Option Nat -> instruction
  | arith aop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, lhsv, rhsv with
      | SmtSort.bitvec n, l, r => assignOptionTerm (arithOpFunc aop l r) -- option as some are unimplemented
      | _, _, _ => BlockVCG.localBlockError "Unexpected sort";
      pure true
    else BlockVCG.localBlockError "Unexpected type"
  | bit bop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, lhsv, rhsv with
      | SmtSort.bitvec n, l, r => assignOptionTerm (bitOpFunc bop l r)
      | _, _, _ => BlockVCG.localBlockError "Unexpected sort";
      pure true
    else BlockVCG.localBlockError "Unexpected type"
  | call tailcall o_ty f args => do
    match f with 
    | LLVM.Value.symbol s =>
      llvmInvoke tailcall s args (match o_ty, stmt.assign with 
                                  | some ty, some i => some (i, ty)
                                  | _, _ => none)
    | _ => localBlockError "VCG currently only supports direct calls.";
    pure true

--   | conv : conv_op -> typed value -> LLVMType -> instruction
  | icmp bop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, stmt.assign, lhsv, rhsv with
      | _, none, _, _ => pure ()
      | SmtSort.bitvec n, some i, l, r => do 
        _ <- defineTerm i (Smt.smtIte (icmpOpFunc bop l r) (Smt.bvimm 1 1) (Smt.bvimm 1 0)); 
        pure ()
      | _, _, _, _ => BlockVCG.localBlockError "Unexpected sort";
      pure true
    else BlockVCG.localBlockError "Unexpected type"

  | br { type := _lty, value := cnd } tlbl flbl => do
    mcExecuteToEnd;
    let pf : HasSMTSort (LLVM.LLVMType.prim (LLVM.PrimType.integer 1)) := rfl;
    cndTerm <- primEval _ pf cnd;
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
    if H : HasSMTSort lty ∧ HasSMTSort rty then do
      lhsv <- primEval lty H.left lhs;
      match asSMTSort lty H.left, asSMTSort rty H.right, cop, lhsv with
      | SmtSort.bitvec n, SmtSort.bitvec m, LLVM.ConvOp.trunc, l => do 
        if H : m <= n -- FIXME: we should move these out of VCGBackend
        then assignTerm (x86.vcg.bitvec.trunc m H l)
        else unimplemented
      | SmtSort.bitvec n, SmtSort.bitvec m, LLVM.ConvOp.zext, l => do 
        assignTerm (x86.vcg.bitvec.uresize n m l)
      | SmtSort.bitvec n, SmtSort.bitvec m, LLVM.ConvOp.sext, l => do 
        assignTerm (x86.vcg.bitvec.sresize n m l)
      | SmtSort.bitvec n, SmtSort.bitvec m, LLVM.ConvOp.int_to_ptr, l => assignTerm l
      | SmtSort.bitvec n, SmtSort.bitvec m, LLVM.ConvOp.ptr_to_int, l => assignTerm l
      | _, _, _, _ => unimplemented;
      pure true
    else BlockVCG.localBlockError "Unexpected type"
  | load addr mOrd mAlign =>
    if mOrd.isSome then BlockVCG.localBlockError "Atomic ordering not yet supported."
    else match stmt.assign with
         | none => BlockVCG.localBlockError "LLVM Load without an assigned identifier."
         | some x => do
           llvmLoad x addr mAlign;
           pure true
  | store (val:Typed Value) (addr:Typed Value) (_align:Option Nat) => do
      addrTerm ← primEvalTypedValueAsBV64 addr;
      ⟨_, valTerm⟩ ← tryPrimEval val.type val.value;
      llvmStore addrTerm valTerm;
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

/-- The statement that either [low1,high1) preceeds and does not overlap
    [low2,high2) or vice versa. --/
def isDisjoint (low1 high1 low2 high2 : Smt.Term SmtSort.bv64)
  : Smt.Term SmtSort.bool :=
Smt.or (Smt.bvule high1 low2) (Smt.bvule high2 low1)


-- | Add the LLVM declarations for an allocation.
def allocaDeclarations
  (a : AllocaAnn)
  : BlockVCG Unit := do
let nm : LocalIdent := a.ident;
let sz := a.size;
-- Get used allocas
used ← BlockVCGState.activeAllocaMap <$> get;
-- Check that alloca name is not in use.
when (used.contains nm) $ localBlockError $ nm.name ++ " is already used as an allocation.";
-- Identifies the LLVM base address of an allocation.
let baseNm : LLVM.Ident := LLVM.Ident.named $ "alloca_" ++ nm.name ++ "_llvm_base";
-- Identifies the LLVM end address of an allocation.
let endNm  : LLVM.Ident := LLVM.Ident.named $ "alloca_" ++ nm.name ++ "_llvm_end";
-- Declare LLVM alloca base and end
baseVar ← declareTerm baseNm SmtSort.bv64;
endVar ← defineTerm endNm (Smt.bvadd baseVar (Smt.bvimm 64 sz));
-- Assert alloca end computation did not overflow.
addAssert $ Smt.bvule baseVar endVar;
let predNm : String := "llvmaddr_in_alloca_" ++ nm.name;
-- Introduce predicate to check LLVM addresses.
rangeCheck ← BlockVCG.defineRangeCheck predNm baseVar endVar;
-- Add assumption that LLVM allocation does not overlap with
-- existing allocations.
used.forM (λ _ a' => addAssert $ isDisjoint baseVar endVar a'.baseAddress a'.endAddress);
-- Define register alloca is returned to.
let regNm : LLVM.Ident := LLVM.Ident.named $ "llvm_" ++ nm.name;
reg ←  defineTerm regNm baseVar;
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
        (m : BlockVCG Unit) : Except BlockVCGError (List VerificationEvent) := do
let blockStart := blockAnn.startAddr.toNat;
let sz := blockAnn.codeSize;
let blockMap : MCBlockAnnMap :=
  (let mk (e : MCMemoryEvent) := (e.addr.toNat, e.info);
   Std.RBMap.ofList (List.map mk blockAnn.memoryEvents.toList));
let ((stdLib, blockRegs), (idGen', script)) := Smt.runSmtM IdGen.empty (do
  let ann := mctx.annotations;
  stdLib <- x86.vcg.MCStdLib.make firstAddr.addr.toNat ann.pageSize ann.stackGuardPageCount blockAnn.allocas;
  blockRegs <-
    if thisBlock = firstBlock
    then pure stdLib.funStartRegs
    else x86.vcg.RegState.declare_const ("a" ++ blockStart.ppHex ++ "_")  blockStart;
  -- FIXME df etc.
  pure (stdLib, blockRegs));
let ctx : BlockVCGContext :=
  { mcModuleVCGContext := mctx
  , llvmFunName := funAnn.llvmFunName
  , funBlkAnnotations := bmap
  , firstBlockLabel := firstBlock
  , currentBlock    := thisBlock
  -- , callbackFns     := prover
  -- ^^ FIXME - upstream code set some settings-related stuff that affected this field
  --            (e.g., are we in interactive or export mode, etc)
  , mcBlockEndAddr  := blockStart + sz
  , mcBlockMap      := blockMap
  , mcStdLib        := stdLib
  };
let s : BlockVCGState :=
  { mcCurAddr := blockStart
  , mcCurSize := 0
  , mcCurRegs := blockRegs
  , mcCurMem  := stdLib.blockStartMem
  , mcEvents  := []
  , idGen := idGen' -- passing idGen' twice here probably isn't ideal (i.e., could introduce name collisions via a bug)
  , llvmInstIndex := 0
  , mcPendingAllocaOffsetMap := blockAnn.allocas
  , activeAllocaMap := Std.RBMap.empty
  , llvmIdentMap  := Std.RBMap.empty
  , smtContext := do set ({revScript := script.reverse, idGen := idGen'} : Smt.SmtState)
  , goalIndex := 0
  , verificationEvents := []
  };
match (m.run ctx).run s with
| EStateM.Result.ok _ s' => Except.ok s'.verificationEvents.reverse
| EStateM.Result.error e s' => Except.error e

end BlockVCG

-- | Verify c over LLVM stmts
--
-- Note. This is written to take a function rather than directly call
-- @stepNextStmtg@ so that the call stack is cleaner.
def checkEachStmt : List LLVM.Stmt → BlockVCG Unit
| [] => BlockVCG.localBlockError "We have reached end of LLVM events without a block terminator."
| (stmt::stmts) => do
  BlockVCG.addComment $ "LLVM: " ++ (ppLLVM stmt);
  keepGoing ← stepNextStmt stmt;
  modify (λ s => {s with llvmInstIndex := s.llvmInstIndex + 1 });
  if keepGoing then checkEachStmt stmts
  else if stmts.isEmpty then pure ()
  else BlockVCG.localBlockError "Expected return to be last LLVM statement."

def defineArgBinding (b : LLVMMCArgBinding) : BlockVCG Unit := do
funStartRegs ← (x86.vcg.MCStdLib.funStartRegs ∘ BlockVCGContext.mcStdLib) <$> read;
let val : Smt.Term SmtSort.bv64 := funStartRegs.get_reg64 b.register;
_ ← defineTerm b.llvmArgName val;
pure ()

def definePhiVar (nm : LLVM.Ident) (entry : LLVM.LLVMType × BlockLabelValMap) : BlockVCG Unit := do
let (tp, _) := entry;
s ← coerceToSMTSort tp;
_ ← declareTerm nm s;
pure ()

/-- Verify a reachable block satisfies its specification. cf `verifyBlock` --/
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
llvmIdentTermMap ← BlockVCGState.llvmIdentMap <$> get;
-- Assume preconditions
blockAnn.preconds.forM (λ pExpr => do
                          pTerm ← evalPrecondition llvmIdentTermMap.find? pExpr;
                          addAssert pTerm);
-- Start processing LLVM statements
checkEachStmt stmts


end ReoptVCG
