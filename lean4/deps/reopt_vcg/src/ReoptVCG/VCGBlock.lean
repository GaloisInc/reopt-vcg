
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import LeanLLVM.PP
import SMTLIB.Syntax
import X86Semantics.Common -- for reg names
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import ReoptVCG.MCStdLib
import ReoptVCG.SMT


namespace ReoptVCG

open LLVM (LLVMType Typed PrimType Value)
open SMT (smtM IdGen.empty)
open SMT.sort (smt_bool)
open x86 (reg64)
open BlockVCG (globalThrow)
open x86.vcg (RegState)

namespace BlockVCG

-- | Stop verifying this block.
def haltBlock {α} (msg : String) : BlockVCG α :=
localThrow msg

-- | This prepends the LLVM and machine code location information for
-- display to user.
def prependLocation (msg : String) : BlockVCG String := do
fnName ← BlockVCGContext.llvmFunName <$> read;
lbl ← BlockVCGContext.currentBlock <$> read;
instIdx ← BlockVCGState.llvmInstIndex <$> get;
curAddr ← BlockVCGState.mcCurAddr <$> get;
pure $ renderMCInstError fnName lbl instIdx curAddr msg


-- | Report an error at the given location and stop verification of
-- this block. FIXME this currently uses a callback (which will report an error via IO)
-- _and_ calls `haltBlock`, which will return a local error with an error message. At
-- some point we probably just want to use the latter when we move away from using IO
-- as much.
def fatalBlockError {α} (msg : String) : BlockVCG α := do
thisInst ← BlockVCGState.llvmInstIndex <$> get;
curAddr ← BlockVCGState.mcCurAddr <$> get;
callback <- ProverInterface.blockErrorCallback <$> BlockVCGContext.callbackFns <$> read;
liftIO $ callback thisInst curAddr msg;
haltBlock msg


def addCommand (cmd : SMT.command) : BlockVCG Unit := do
  prover <- (fun (s : BlockVCGContext) => s.callbackFns) <$> read;
  liftIO $ prover.addCommandCallback cmd

def runsmtM {a : Type} (m : smtM a) : BlockVCG a := do
  let run' := fun (s : BlockVCGState) => 
                  (let r  := SMT.runsmtM s.idGen m;
                       ((r.fst, r.snd.snd.reverse)
                       , {s with idGen := r.snd.fst}));
  (r, cmds) <- modifyGet run';
  _ <- List.mapM addCommand cmds;
  pure r

-- | Add assertion that the propositon is true without requiring it to be proven.
def addAssert (p : SMT.term smt_bool) : BlockVCG Unit := 
  addCommand $ SMT.Raw.command.assert p -- FIXME

-- | @proveTrue p msg@ adds a proof obligation @p@ is true for all
-- interpretations of constants with the message @msg@.
def proveTrue (p : SMT.term smt_bool) (msg : String) : BlockVCG Unit := do
  annMsg <- prependLocation msg;
  prover <- BlockVCGContext.callbackFns <$> read;
  liftIO $ prover.proveTrueCallback p annMsg;
  -- Add command for future proofs
  addAssert p

-- | @proveEq x y msg@ add a proof obligation named @msg@ asserting
-- that @x@ equals @y@.
def proveEq {s : SMT.sort} (x y : SMT.term s) (msg : String) : BlockVCG Unit := do
  prover <- BlockVCGContext.callbackFns <$> read;
  annMsg <- prependLocation msg;
  liftIO $ prover.proveTrueCallback (SMT.eq x y) annMsg; -- FIXME: was proveFalseCallback/SMT.distinct
  -- Add command for future proofs
  addAssert (SMT.eq x y)

-- | Add assertion that the propositon is true without requiring it to be proven.
def addComment (str : String) : BlockVCG Unit :=
  addCommand $ SMT.Raw.command.comment str -- FIXME?


end BlockVCG

export BlockVCG (addCommand proveTrue proveEq addAssert addComment)

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
def asSMTSort : forall (tp : LLVMType) (pf : HasSMTSort tp), SMT.sort
| LLVM.LLVMType.ptr _, _  => SMT.sort.bitvec 64
| LLVM.LLVMType.prim (LLVM.PrimType.integer i), _ => SMT.sort.bitvec i

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

def asSMTSort' (tp : LLVMType) : Option SMT.sort :=
  if H : HasSMTSort tp then some (asSMTSort tp H) else none

def coerceToSMTSort (ty : LLVMType) : BlockVCG SMT.sort :=
  match asSMTSort' ty with
  | some tp => pure tp
  | none    => BlockVCG.globalThrow $ "Unexpected type " ++ (ppLLVM ty)

--------------------------------------------------------------------------------
-- Ident <-> SMT

def lookupIdent (i : LLVM.Ident) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  m <- BlockVCGState.llvmIdentMap <$> get;
  match m.find? i with
  | some (Sigma.mk s' tm) => 
    if H : s' = s then pure (Eq.recOn H tm) else BlockVCG.globalThrow ("Sort mismatch for " ++ i.asString)
  | none => BlockVCG.globalThrow ("Unknown ident: " ++ i.asString)

def freshIdent (i : LLVM.Ident) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  sym <- BlockVCG.runsmtM (SMT.freshSymbol i.asString); -- FIXME: this should be primitive in SMT
  let tm := SMT.mk_symbol sym s;
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ tm)});
  pure tm

def defineTerm {s : SMT.sort} (i : LLVM.Ident) (tm : SMT.term s) : BlockVCG (SMT.term s) := do
  sym <- BlockVCG.runsmtM (SMT.define_fun i.asString [] s tm);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym

def declareTerm (i : LLVM.Ident) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  sym <- BlockVCG.runsmtM (SMT.declare_fun i.asString [] s);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym


--------------------------------------------------------------------------------
-- MC Events

section

open x86.vcg (Event)
open x86.vcg.Event
open BlockVCG (liftIO globalThrow)

def mcNextAddr (s : BlockVCGState) : MemAddr := s.mcCurAddr + s.mcCurSize

-- | Get next events
def getNextEvents : BlockVCG Unit := do
  ctx <- read;
  s <- get;
  let addr := mcNextAddr s;
  when (not (addr < ctx.mcBlockEndAddr)) $ 
    globalThrow $ "Unexpected end of machine code events.";
  -- FIXMEL df, x87Top
  -- BlockVCG.liftIO $ IO.println ("Decoding at " ++ addr.ppHex);

  addComment ("MC: at " ++ addr.ppHex);

  (events, idGen', sz) <-
    match x86.vcg.instructionEvents ctx.mcBlockMap s.mcCurRegs s.idGen addr
            ctx.mcModuleVCGContext.decoder with
    | Except.error e => globalThrow e
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


def getSupportedType (s : SMT.sort) : BlockVCG (x86.vcg.SupportedMemType s) := do
  mcstd  <- BlockVCGContext.mcStdLib <$> read;
  let mops := mcstd.memOpsBySort;
  match mops s with
  | some ops => pure ops
  | none => globalThrow $ "Unexpected type " ++ toString s

def declareMem : BlockVCG x86.vcg.memory :=
  BlockVCG.runsmtM $ SMT.declare_fun "mem" [] x86.vcg.memory_t

def mcWrite (addr : x86.vcg.memaddr) (s : SMT.sort) (val : SMT.term s) : BlockVCG Unit := do
  curMem <- (fun (s : BlockVCGState) => s.mcCurMem) <$> get;
  supType <- getSupportedType s;
  nextMem <- BlockVCG.runsmtM $ SMT.define_fun "mem" [] x86.vcg.memory_t (supType.writeMem curMem addr val);
  modify $ fun s => { s with mcCurMem := nextMem }

def mcRead (addr : x86.vcg.memaddr) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  curMem <- BlockVCGState.mcCurMem <$> get;
  supType <- getSupportedType s;
  pure (supType.readMem curMem addr)

def mcAssignRead (addr : x86.vcg.memaddr) (s : SMT.sort) (smtVar : SMT.term s) : BlockVCG Unit := do
  v <- mcRead addr s;
  addAssert (SMT.eq smtVar v)

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
      liftIO $ IO.println msg;
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
          proveTrue (stdLib.onStack mcAddr (SMT.bvimm _ (n / 8)))
            ("machine code read at " ++ thisIP.ppHex ++ " is not within stack space."));

      -- Define value from reading Macaw heap
      mcAssignRead mcAddr (SMT.sort.bitvec n) smtValVar;
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
          proveTrue (stdLib.onStack mcAddr (SMT.bvimm _ (n / 8)))
            ("machine code write at " ++ thisIP.ppHex ++ " is in unreserved stack space."));

      -- do addr <- mcCurAddr <$> get;
      --    proveTrue (evalRangeCheck mcOnlyStackRange mcAddr (memReprBytes tp)) $
      --      printf "machine code write at %s is in unreserved stack space." (show addr)
      -- Update stack with write.
      mcWrite mcAddr (SMT.sort.bitvec n) smtVal;
      -- Process next events
      modify $ fun s => {s with mcEvents := mevs };
      execMCOnlyEvents endAddr
    -- This checks to see if the next instruction jumps to the next ip,
    -- and if so it runs it.
  | FetchAndExecuteEvent regs :: mevs => do
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: fetch and exec case");
      when (not mevs.isEmpty) $ globalThrow "MC event after fetch and execute";
      modify $ fun s => { s with mcEvents := [] };
      -- Update registers
      setMCRegs regs;
      -- Process next events
      nextAddr <- mcNextAddr <$> get;
      -- BlockVCG.liftIO $ IO.println ("execMCOnlyEvents: fetch and exec case: " ++ nextAddr.ppHex ++ " " ++ endAddr.ppHex);

      -- FIXME: this is fragile ...
      match SMT.bvAsConst regs.ip with
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

-- -- | Get the next MC event that could interact with LLVM.
-- popMCEvent :: HasCallStack => BlockVCG M.Event
-- popMCEvent = do
--   endAddr <- asks mcBlockEndAddr
--   execMCOnlyEvents endAddr
--   evts <- gets mcEvents
--   case evts of
--     [] -> do
--       error "Reached end of block"
--     (h:r) -> do
--       modify $ \s -> s { mcEvents = r }
--       pure h

end


-- -- | Move to end of current block.
def mcExecuteToEnd : BlockVCG Unit := do
  endAddr <- (fun (s : BlockVCGContext) => s.mcBlockEndAddr) <$> read;
  execMCOnlyEvents endAddr;
  evts <- (fun (s : BlockVCGState) => s.mcEvents) <$> get;
  match evts with
  | [] => pure ()
  | e :: _ => BlockVCG.globalThrow $ "Expecting end of block, got " ++ repr e

--------------------------------------------------------------------------------
-- Literal constructors

def mkInt {w : Nat} (v : Int) (H : w > 0)
  : SMT.term (asSMTSort (LLVM.LLVMType.prim (LLVM.PrimType.integer w)) H) :=
  SMT.bvimm' w v

section
open LLVM.Value

def primEval : forall (tp : LLVMType) (H :HasSMTSort tp), Value -> BlockVCG (SMT.term (asSMTSort tp H))
| tp, H, ident i => lookupIdent i (asSMTSort tp H)
| LLVM.LLVMType.prim (LLVM.PrimType.integer w), H, integer i => pure (mkInt i H)
| _, _, _ => BlockVCG.globalThrow "unimplemented"

end

-- --------------------------------------------------------------------------------
-- -- Branch support


-- AMK: `initBlockRegValues` is used in the Haskell implementation of `verifyBlockPreconditions`
--      ... but for ours I just use a helper `checkInitRegVals` since there isn't an obvious
--      analogue to the `X86Reg` from flexdis86 (i.e., a way to index the IP, X87 top reg, and DF)..
-- def initBlockRegValues (ann : ReachableBlockAnn) : List (Fin 16 × SMT.term (SMT.sort.bitvec 64)) :=
--   [ (Some X86_IP,     SMT.bvhexadecimal (toInteger (Ann.blockAddr blockAnn)) 64)
--   -- , (Some X87_TopReg, SMT.bvdecimal (toInteger (Ann.blockX87Top blockAnn)) 3)
--   -- , (Some DF,         if Ann.blockDFFlag blockAnn then SMT.true else SMT.false)
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
  : BlockVCG (PSigma (fun (H : HasSMTSort ty) => SMT.term (asSMTSort ty H))) := 
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
           let smcv0 := SMT.extract (i - 1) 0 w;
           let r := @Eq.recOn _ _ (fun a _ => SMT.term (SMT.sort.bitvec a)) _ pf' smcv0;
           pure (PSigma.mk pf r)
   else globalThrow "Unexpected sort in wordAsType"
| _ => globalThrow "Unexpected sort in wordAsType"
  
def proveRegRel (msg : String) (w : x86.vcg.bitvec 64)
  : LLVM.Typed LLVM.Value ->  BlockVCG Unit
| { type := ty, value := v } => do  
  PSigma.mk pf mcv <- wordAsType w ty;
  lv <- primEval ty pf v;
  proveEq lv mcv msg

def llvmReturn (mlret : Option (Typed Value)) : BlockVCG Unit := do
  mcExecuteToEnd;
  regs <- BlockVCGState.mcCurRegs <$> get;
  _ <- (do sht  <- stackHighTerm;
           proveEq (regs.get_reg64 x86.reg64.rsp) (SMT.bvadd sht (SMT.bvimm _ 8))
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
  when isTailCall $ globalThrow "Tail calls are unimplemented";

  BlockVCGContext.mcBlockEndAddr <$> read >>= execMCOnlyEvents;

  regs <- BlockVCGState.mcCurRegs <$> get;

  --------------------
  -- Pre call

  -- FIXME assertFnNameEq fsym regs.ip
  when (args.size > x86ArgGPRegs.length) $ 
    globalThrow "Too many arguments";

  let proveOne v (r : x86.reg64) := 
    proveRegRel ("argument matches register " ++ r.repr) (regs.get_reg64 r) v;
  List.forM₂ proveOne args.toList x86ArgGPRegs;

  -- FIXME checkDirectionFlagClear;
  postCallRIP  <- mcNextAddr <$> get;

  -- FIXME: generalise returnAddrTerm?
  -- Check stored return value matches next instruction
  (do addrOnStack <- mcRead (regs.get_reg64 x86.reg64.rsp) _;
      proveEq addrOnStack (SMT.bvimm 64 postCallRIP) "return address matches next instruction.");
        
  --------------------
  -- Post call

  -- Construct new register after the call.
  let postCallRSP := SMT.bvadd (regs.get_reg64 x86.reg64.rsp) (SMT.bvimm _ 8);
  -- create a 
  newRegs <- (do rs <- BlockVCG.runsmtM $ 
                       x86.vcg.RegState.declare_const ("a" ++ postCallRIP.ppHex  ++ "_")  postCallRIP;
                 let rs_with_rsp := x86.vcg.RegState.update_reg64 x86.reg64.rsp (fun _ => postCallRSP) rs;
                 let copy_reg s r := x86.vcg.RegState.update_reg64 r (fun _ => regs.get_reg64 r) s;
                 pure (List.foldl copy_reg rs_with_rsp x86CalleeSavedGPRegs));

  modify $ fun s => {s with mcCurRegs := newRegs };

  -- Update machine code memory to post-call memory.
  (do newMem <- declareMem;
      oldMem <- BlockVCGState.mcCurMem <$> get;
      sht    <- stackHighTerm;
      addAssert $ SMT.eqrange newMem oldMem postCallRSP (SMT.bvadd sht (SMT.bvimm _ 7));
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
                          -> SMT.term (SMT.sort.bitvec n)
                          -> SMT.term (SMT.sort.bitvec n)
                          -> SMT.term (SMT.sort.bitvec n)
| LLVM.ArithOp.add _ _, x, y => SMT.bvadd x y
| LLVM.ArithOp.sub _ _, x, y => SMT.bvsub x y
| LLVM.ArithOp.mul _ _, x, y => SMT.bvmul x y
| _, _, _ =>  SMT.bvimm _ 0 -- FIXME


def bitOpFunc {n : Nat} : LLVM.BitOp
                        -> SMT.term (SMT.sort.bitvec n)
                        -> SMT.term (SMT.sort.bitvec n)
                        -> SMT.term (SMT.sort.bitvec n)
| LLVM.BitOp.and, x, y => SMT.bvand x y
| LLVM.BitOp.or, x, y  => SMT.bvor x y
| LLVM.BitOp.xor, x, y => SMT.bvxor x y
| _, _, _ =>  SMT.bvimm _ 0 -- FIXME

def icmpOpFunc {n : Nat} : LLVM.ICmpOp
                         -> SMT.term (SMT.sort.bitvec n)
                         -> SMT.term (SMT.sort.bitvec n)
                         -> SMT.term smt_bool
| ieq, x, y  => SMT.eq x y
| ine, x, y  => SMT.not (SMT.eq x y)
| iugt, x, y => SMT.bvugt x y
| iuge, x, y => SMT.bvuge x y 
| iult, x, y => SMT.bvult x y 
| iule, x, y => SMT.bvule x y 
| isgt, x, y => SMT.bvsgt x y 
| isge, x, y => SMT.bvsge x y 
| islt, x, y => SMT.bvslt x y 
| isle, x, y => SMT.bvsle x y 

end

def tryPrimEval (tp : LLVMType) (v:Value) : BlockVCG (Sigma SMT.term) :=
if h : HasSMTSort tp
then do
  t ← primEval tp h v;
  pure $ ⟨asSMTSort tp h, t⟩
else
  BlockVCG.globalThrow $ "unable to evaluate llvm term "++(ppLLVM v)++" at type "++(ppLLVM tp)


--------------------------------------------------------------------------------
-- Block Precondition Verification


namespace BlockVCG


-- def checkInitRegVals
-- (blockAnn : ReachableBlockAnn)
-- -- ^ Message to preface verification comments/messages/etc
-- (goalFn : SMT.term SMT.sort.smt_bool → SMT.term SMT.sort.smt_bool)
--  : BlockVCG Unit := do
-- -- Check the instruction pointer
-- let expectedIp : SMT.term SMT.sort.bv64 := SMT.bvimm 64 blockAnn.startAddr.toNat;
-- regs <- BlockVCGState.mcCurRegs <$> get;               
-- proveTrue (goalFn (SMT.eq expectedIp regs.ip)) "Checking the IP register.";

-- -- Check x87Top value
-- --let expectedX87Top : SMT.term SMT.sort.bv64 := SMT.bv 64 blockAnn.startAddr.toNat;
-- -- (Some X87_TopReg, SMT.bvdecimal (toInteger (Ann.blockX87Top blockAnn)) 3)
-- -- FIXME check BlockVCGState.mcX87Top value against expected ^
-- -- Check the direction flag
-- --let expectedDF : SMT.term SMT.sort.bv64 := SMT.bvimm 64 blockAnn.startAddr.toNat;
-- -- (Some DF,         if Ann.blockDFFlag blockAnn then SMT.true else SMT.false)
-- -- FIXME check BlockVCGState.mcDF value against expected ^
-- pure ()

-- cf. `verifyBlockPreconditions`
def verifyPreconditions
(prefixDescr : String)
-- ^ Message to preface verification comments/messages/etc
(goalFn : SMT.term SMT.sort.smt_bool → SMT.term SMT.sort.smt_bool)
-- ^ Function applied to predicates before verification allowing us
-- to conditionally validate some of the preconditions.
(lbl : LLVM.BlockLabel)
-- ^ LLVM label of the block we are jumping to.
: BlockVCG Unit := do
blkMap ← BlockVCGContext.funBlkAnnotations <$> read;
match findBlock blkMap lbl with
| none =>
  fatalBlockError $ "Target block "++(ppBlockLabel lbl)++" lacks annotations."
| some (BlockAnn.unreachable, _) =>
  proveTrue (goalFn SMT.false) $ "target block "++(ppBlockLabel lbl)++"is unreachable."
| some (BlockAnn.reachable tgtBlockAnn, varMap) => do
  firstLabel ← BlockVCGContext.firstBlockLabel <$> read;
  -- Ensure we're not in the first block
  when (lbl == firstLabel) $ globalThrow "LLVM should not jump to first label in function.";
  -- Check initialized register values (just rip for now)
  (do regs <- BlockVCGState.mcCurRegs <$> get;
      let expected := SMT.bvimm 64 tgtBlockAnn.startAddr.toNat;
      proveTrue (goalFn (SMT.eq expected regs.ip))
        (prefixDescr ++ " register rip."));

  -- checkInitRegVals tgtBlockAnn goalFn;

  srcLbl <- BlockVCGContext.currentBlock <$> read;
  -- Resolve terms for SMT variables which can appear in precondition statements.
  let resolvePhiVarVal : LLVM.Ident → (LLVM.LLVMType × BlockLabelValMap) → BlockVCG (Sigma SMT.term) :=
    λ nm val => let (tp, valMap) := val;
                match valMap.find? srcLbl with
                | some v => tryPrimEval tp v
                | none => globalThrow $ "Could not find initial value of llvm variable `"++nm.asString++"`.";
  phiTermMap ← varMap.mapM resolvePhiVarVal;
  -- Verify each precondition
  tgtBlockAnn.preconds.forM (λ precondExpr => do
                               p ← evalPrecondition phiTermMap.find? precondExpr;
                               proveTrue (goalFn p) $ prefixDescr++" precondition: "++precondExpr.toString)
  -- Check allocations are preserved. -- FIXME actually do this when we get to reasoning about allocas.
  -- curAllocas <- gets mcPendingAllocaOffsetMap
  -- when (Ann.blockAllocas tgtBlockAnn /= curAllocas) $ do
  --   fatalBlockError $ printf "Allocations in jump to %s do not match." (ppBlock lbl)


end BlockVCG



--------------------------------------------------------------------------------
-- stepNextStmt

section
open LLVM.Instruction
open BlockVCG (verifyPreconditions)

def stepNextStmt (stmt : LLVM.Stmt) : BlockVCG Bool := do
  match stmt.instr with
  | phi _ _ => globalThrow "Unexpected phi in stepNextStmt"
--   | alloca : LLVMType -> Option (typed value) -> Option Nat -> instruction
  | arith aop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, stmt.assign, lhsv, rhsv with
      | _, none, _, _ => pure ()
      | SMT.sort.bitvec n, some i, l, r => do 
        _<- defineTerm i (arithOpFunc aop l r); 
        pure ()
      | _, _, _, _ => BlockVCG.globalThrow "Unexpected sort";
      pure true
    else BlockVCG.globalThrow "Unexpected type"
  | bit bop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, stmt.assign, lhsv, rhsv with
      | _, none, _, _ => pure ()
      | SMT.sort.bitvec n, some i, l, r => do 
        _ <- defineTerm i (bitOpFunc bop l r);
        pure ()
      | _, _, _, _ => BlockVCG.globalThrow "Unexpected sort";
      pure true
    else BlockVCG.globalThrow "Unexpected type"
  | call tailcall o_ty f args => do
    match f with 
    | LLVM.Value.symbol s =>
      llvmInvoke tailcall s args (match o_ty, stmt.assign with 
                                  | some ty, some i => some (i, ty)
                                  | _, _ => none)
    | _ => globalThrow "VCG currently only supports direct calls.";
    pure true

--   | conv : conv_op -> typed value -> LLVMType -> instruction
  | icmp bop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, stmt.assign, lhsv, rhsv with
      | _, none, _, _ => pure ()
      | SMT.sort.bitvec n, some i, l, r => do 
        _ <- defineTerm i (SMT.smt_ite (icmpOpFunc bop l r) (SMT.bvimm 1 1) (SMT.bvimm 1 0)); 
        pure ()
      | _, _, _, _ => BlockVCG.globalThrow "Unexpected sort";
      pure true
    else BlockVCG.globalThrow "Unexpected type"

  | br { type := _lty, value := cnd } tlbl flbl => do
    mcExecuteToEnd;
    let pf : HasSMTSort (LLVM.LLVMType.prim (LLVM.PrimType.integer 1)) := rfl;
    cndTerm <- primEval _ pf cnd;
    let c := SMT.eq cndTerm (SMT.bvimm _ 1);
    verifyPreconditions "true branch"  (SMT.impl c)           tlbl;
    verifyPreconditions "false branch" (SMT.impl (SMT.not c)) flbl;
    pure false
  
  | jump lbl => do
    mcExecuteToEnd;
    verifyPreconditions "jump"  (fun x => x) lbl;
    pure false

  | ret v    => do llvmReturn (some v); pure false
  | retVoid  => do llvmReturn none; pure false
  | _ => BlockVCG.globalThrow "(stepNextStmt) unimplemented"
  

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
        (m : BlockVCG Unit) : IO Unit := do
  mctx.proverGen.blockCallback funAnn.llvmFunName thisBlock $ fun prover => do
    let blockStart := blockAnn.startAddr.toNat;
    let sz := blockAnn.codeSize;
    let blockMap : MCBlockAnnMap := 
      (let mk (e : MCMemoryEvent) := (e.addr.toNat, e.info);
       Std.RBMap.ofList (List.map mk blockAnn.memoryEvents.toList));
       
    ((stdLib, blockRegs), idGen') <- prover.runsmtM IdGen.empty (do
      let ann := mctx.annotations;  
      stdLib <- x86.vcg.MCStdLib.make firstAddr.addr.toNat ann.pageSize ann.stackGuardPageCount;
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
      , callbackFns     := prover
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
      , idGen := idGen'
      , llvmInstIndex := 0
      , llvmIdentMap  := Std.RBMap.empty
      };
     r <- ((m.run ctx).run' s).run;
     match r with
     | Except.ok _ => pure ()
     | Except.error e => match e with
       | BlockVCGError.localErr msg =>
         IO.println $ "Local error encountered during BlockVCG.run: " ++ msg
       | BlockVCGError.globalErr msg =>
         throw $ IO.userError $ "Fatal error encountered in BlockVCG.run: " ++ msg

end BlockVCG

-- | Verify c over LLVM stmts
--
-- Note. This is written to take a function rather than directly call
-- @stepNextStmtg@ so that the call stack is cleaner.
def checkEachStmt : List LLVM.Stmt → BlockVCG Unit
| [] => BlockVCG.globalThrow "We have reached end of LLVM events without a block terminator."
| (stmt::stmts) => do
  BlockVCG.addComment $ "LLVM: " ++ (ppLLVM stmt);
  continue ← stepNextStmt stmt;
  modify (λ s => {s with llvmInstIndex := s.llvmInstIndex + 1 });
  if continue then
    checkEachStmt stmts
   else
    unless stmts.isEmpty $ BlockVCG.globalThrow "Expected return to be last LLVM statement."

def defineArgBinding (b : LLVMMCArgBinding) : BlockVCG Unit := do
funStartRegs ← (x86.vcg.MCStdLib.funStartRegs ∘ BlockVCGContext.mcStdLib) <$> read;
let val : SMT.term SMT.sort.bv64 := funStartRegs.get_reg64 b.register;
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
-- FIXME we skip alloca stuff for now, FYI.
-- forM_ (Ann.blockAllocas blockAnn) $ \a  -> do
--   when (Ann.allocaExisting a) $ do
--     allocaDeclarations (Ann.allocaIdent a) (SMT.bvdecimal (toInteger (Ann.allocaSize a)) 64)
--
-- Declare LLVM arguments in terms of the registers at function start.
args.forM defineArgBinding;
-- Declare phi variables
phiVarMap.mfor definePhiVar;
llvmIdentTermMap ← BlockVCGState.llvmIdentMap <$> get;
-- -- Assume preconditions
blockAnn.preconds.forM (λ pExpr => do
                          pTerm ← evalPrecondition llvmIdentTermMap.find? pExpr;
                          addAssert pTerm);
-- -- Start processing LLVM statements
checkEachStmt stmts


end ReoptVCG
