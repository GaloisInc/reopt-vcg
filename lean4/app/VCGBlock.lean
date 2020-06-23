
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import SMTLIB.Syntax
import X86Semantics.Common -- for reg names
import ReoptVCG.Types
import ReoptVCG.VCGBackend
import ReoptVCG.WordSize
import ReoptVCG.MCStdLib

namespace ReoptVCG

open llvm (llvm_type typed prim_type value)
open SMT (smtM)
open SMT.sort (smt_bool)
open x86 (reg64)

namespace BlockVCG

def addCommand (cmd : SMT.command) : BlockVCG Unit := do
  prover <- (fun (s : BlockVCGContext) => s.callbackFns) <$> read;
  liftIO $ prover.addCommandCallback cmd

def runsmtM {a : Type} (m : smtM a) : BlockVCG a := do
  let run' := fun (s : BlockVCGState) => 
                  (let r  := SMT.runsmtM s.mcLocalIndex m;
                       ((r.fst, r.snd.snd.reverse)
                       , {s with mcLocalIndex := r.snd.fst}));
  (r, cmds) <- modifyGet run';
  _ <- List.mapM addCommand cmds;
  pure r

-- | Add assertion that the propositon is true without requiring it to be proven.
def addAssert (p : SMT.term smt_bool) : BlockVCG Unit := 
  addCommand $ SMT.Raw.command.assert p -- FIXME

-- | @proveTrue p msg@ adds a proof obligation @p@ is true for all
-- interpretations of constants with the message @msg@.
def proveTrue (p : SMT.term smt_bool) (msg : String) : BlockVCG Unit := do
  -- annMsg <- prependLocation msg
  prover <- (fun (s : BlockVCGContext) => s.callbackFns) <$> read;
  liftIO $ prover.proveTrueCallback p msg;
  -- Add command for future proofs
  addAssert p

-- | @proveEq x y msg@ add a proof obligation named @msg@ asserting
-- that @x@ equals @y@.
def proveEq {s : SMT.sort} (x y : SMT.term s) (msg : String) : BlockVCG Unit := do
  prover <- (fun (s : BlockVCGContext) => s.callbackFns) <$> read;
  --  annMsg <- prependLocation msg
  liftIO $ prover.proveTrueCallback (SMT.eq x y) msg; -- FIXME: was proveFalseCallback/SMT.distinct
  -- Add command for future proofs
  addAssert (SMT.eq x y)

end BlockVCG

export BlockVCG (addCommand proveTrue proveEq addAssert)

--------------------------------------------------------------------------------
-- Type <-> SMT

@[reducible]
def HasSMTSort : llvm_type -> Prop
| llvm.llvm_type.ptr_to _  => True
| llvm.llvm_type.prim_type pt  => 
  match pt with
  | llvm.prim_type.integer i => i > 0
  | _ => False
| _ => False

-- | Convert LLVM type to SMT sort.
def asSMTSort : forall (tp : llvm_type) (pf : HasSMTSort tp), SMT.sort
| llvm.llvm_type.ptr_to _, _  => SMT.sort.bitvec 64
| llvm.llvm_type.prim_type (llvm.prim_type.integer i), _ => SMT.sort.bitvec i

namespace HasSMTSort

open llvm.llvm_type
open llvm.prim_type

protected 
def dec : forall (tp : llvm_type), Decidable (HasSMTSort tp)
| ptr_to t  => isTrue True.intro
| prim_type pt => 
  match pt with 
  | integer i    => Nat.decLt _ _
  | label        => isFalse (fun x => x) 
  | token        => isFalse (fun x => x) 
  | void         => isFalse (fun x => x) 
  | float_type _ => isFalse (fun x => x) 
  | x86mmx       => isFalse (fun x => x) 
  | metadata     => isFalse (fun x => x) 
| alias _        => isFalse (fun x => x)  
| array _ _      => isFalse (fun x => x)  
| fun_ty _ _ _   => isFalse (fun x => x)  
| struct _ _     => isFalse (fun x => x)  
| vector _ _     => isFalse (fun x => x)  

instance {tp : llvm_type} : Decidable (HasSMTSort tp) := HasSMTSort.dec tp

end HasSMTSort

def asSMTSort' (tp : llvm_type) : Option SMT.sort :=
  if H : HasSMTSort tp then some (asSMTSort tp H) else none

def coerceToSMTSort (ty : llvm_type) : BlockVCG SMT.sort :=
  match asSMTSort' ty with
  | some tp => pure tp
  | none    => throw ("Unexpected type ")

--------------------------------------------------------------------------------
-- Ident <-> SMT

def lookupIdent (i : llvm.ident) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  m <- (fun (s : BlockVCGState) => s.llvmIdentMap) <$> get;
  match m.find? i with
  | some (Sigma.mk s' tm) => 
    if H : s' = s then pure (Eq.recOn H tm) else throw ("Sort mismatch for " ++ i.asString)
  | none => throw ("Unknown ident: " ++ i.asString)

def freshIdent (i : llvm.ident) (s : SMT.sort) : BlockVCG (SMT.term s) := do
  sym <- BlockVCG.runsmtM (SMT.freshSymbol i.asString);
  let tm := SMT.mk_symbol sym s;
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ tm)});
  pure tm

def defineTerm {s : SMT.sort} (i : llvm.ident) (tm : SMT.term s) : BlockVCG (SMT.term s) := do
  sym <- BlockVCG.runsmtM (SMT.define_fun i.asString [] s tm);
  modify (fun s => {s with llvmIdentMap := s.llvmIdentMap.insert i (Sigma.mk _ sym)});
  pure sym



--------------------------------------------------------------------------------
-- MC Events

section

open x86.vcg (Event)
open x86.vcg.Event
open BlockVCG (liftIO)

def mcNextAddr (s : BlockVCGState) : MemAddr := s.mcCurAddr + s.mcCurSize

-- | Get next events
def getNextEvents : BlockVCG Unit := do
  ctx <- read;
  s <- get;
  let addr := mcNextAddr s;
  when (not (addr < ctx.mcBlockEndAddr)) $ do
    throw $ "Unexpected end of machine code events.";
  -- FIXMEL df, x87Top
  (events, nextIdx, sz) <-
    match x86.vcg.instructionEvents ctx.mcBlockMap s.mcCurRegs s.mcLocalIndex addr 
            ctx.mcModuleVCGContext.decoder with
    | Except.error e => throw e
    | Except.ok    r => pure r;
  -- Update local index and next addr
  set $ { s with mcLocalIndex := nextIdx
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

section
open WordSize
def getSupportedType (s : SMT.sort) : BlockVCG (x86.vcg.SupportedMemType s) := do
  mcstd  <- BlockVCGContext.mcStdLib <$> read;
  let mops := mcstd.memOps;
  match s with
  | SMT.sort.bitvec 8  => pure $ mops word8
  | SMT.sort.bitvec 16 => pure $ mops word16
  | SMT.sort.bitvec 32 => pure $ mops word32
  | SMT.sort.bitvec 64 => pure $ mops word64
  | _ => throw $ "Unexpected type " ++ toString s
end

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
  evts <- (fun (s : BlockVCGState) => s.mcEvents) <$> get;
  match evts with
  | Command cmd :: mevs => do
      addCommand cmd;
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr
  | Warning msg :: mevs => do
      liftIO $ IO.println msg;
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr
  | MCOnlyStackReadEvent mcAddr n smtValVar :: mevs => do
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

      -- FIXME: add stack range stuff
      -- do thisIP <- (fun (s : BlovkVCGState) => s.mcCurAddr) <$> get;
      --    proveTrue (evalRangeCheck onStack mcAddr (memReprBytes tp)) $
      --      printf "Machine code read at %s is not within stack space." (show thisIP)

      -- Define value from reading Macaw heap
      mcAssignRead mcAddr (SMT.sort.bitvec n) smtValVar;
      -- Process future events.
      modify (fun s => { s with mcEvents := mevs });
      execMCOnlyEvents endAddr

    -- Every LLVM write should have a machine code write (but not
    -- necessarily vice versa), we pattern match on machine code
    -- writes.
  | MCOnlyStackWriteEvent mcAddr n smtVal :: mevs => do
      -- We need to assert that this werite will not be visible to LLVM.

      -- FIXME
      -- do addr <- mcCurAddr <$> get;
      --    proveTrue (evalRangeCheck mcOnlyStackRange mcAddr (memReprBytes tp)) $
      --      printf "Machine code write at %s is in unreserved stack space." (show addr)
      -- Update stack with write.
      mcWrite mcAddr (SMT.sort.bitvec n) smtVal;
      -- Process next events
      modify $ fun s => {s with mcEvents := mevs };
      execMCOnlyEvents endAddr
    -- This checks to see if the next instruction jumps to the next ip,
    -- and if so it runs it.
  | FetchAndExecuteEvent regs :: mevs => do
      when (not mevs.isEmpty) $ do
        throw "MC event after fetch and execute";
      modify $ fun s => { s with mcEvents := [] };
      -- Update registers
      setMCRegs regs;
      -- Process next events
      nextAddr <- mcNextAddr <$> get;
      -- FIXME: assert the IP is nextAddr (no jmp etc.)
      if nextAddr < endAddr 
      then do getNextEvents; execMCOnlyEvents endAddr
      else pure ()
      -- case valueAsMemAddr (regs^.boundValue X86_IP) of
      --   Just ipAddr | ipAddr == nextAddr && addrLt nextAddr endAddr -> do
      --                   getNextEvents
      --                   execMCOnlyEvents endAddr
      --   _ -> do
      --     pure ()
  | [] => do
      nextAddr <- mcNextAddr <$> get;
      when (nextAddr < endAddr) $ do
        getNextEvents;
        execMCOnlyEvents endAddr
  |  _ :: _ => pure ()

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
  | _ :: _ => throw $ "Expecting end of block"

--------------------------------------------------------------------------------
-- Literal constructors

def mkInt {w : Nat} (v : Int) (H : w > 0)
  : SMT.term (asSMTSort (llvm.llvm_type.prim_type (llvm.prim_type.integer w)) H) :=
  SMT.bvimm' w v

section
open llvm.value

def primEval : forall (tp : llvm_type) (H :HasSMTSort tp), value -> BlockVCG (SMT.term (asSMTSort tp H))
| tp, H, ident i => lookupIdent i (asSMTSort tp H)
| llvm.llvm_type.prim_type (llvm.prim_type.integer w), H, integer i => pure (mkInt i H)
| _, _, _ => throw "unimplemented"

end

-- --------------------------------------------------------------------------------
-- -- Branch support

-- -- | Register values initialized from annotations.
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

def llvmReturn (mlret : Option (typed value)) : BlockVCG Unit := do
  mcExecuteToEnd;
  regs <- BlockVCGState.mcCurRegs <$> get;
  _ <- (do sht  <- stackHighTerm;
           proveEq (regs.get_reg64 x86.reg64.rsp) sht 
             "Stack height at return matches init.");
  _ <- (do ra <- returnAddrTerm;
           proveEq regs.ip ra "Return address matches entry value.");
  
  -- FIXME checkDirectionFlagClear
  stdLib <- BlockVCGContext.mcStdLib <$> read;
  let rEq r := proveEq (regs.get_reg64 r) (stdLib.funStartRegs.get_reg64 r)
                  ("Value of " ++ r.name ++ " at return is preserved.");
  List.forM rEq x86CalleeSavedGPRegs;
  
  match mlret with
  | none => pure ()
  | some { type := llvmTy, value := v } =>
      let rax := regs.get_reg64 x86.reg64.rax;
      (match llvmTy with
      | ty@(llvm.llvm_type.ptr_to _) => do
          let pf : HasSMTSort ty := True.intro;
          lret <- primEval ty pf v;
          proveEq lret rax "Return values match"
      | ty@(llvm.llvm_type.prim_type (llvm.prim_type.integer 64)) => do
          let pf : HasSMTSort ty := rfl; -- 0 < 64 = true, unfortunately
          lret <- primEval ty pf v;
          proveEq lret rax "Return values match"
      | ty@(llvm.llvm_type.prim_type (llvm.prim_type.integer i)) => do
          if H : 0 < i /\ i < 64                                     
          then do let pf : HasSMTSort ty := H.left;
                  lret <- primEval ty pf v;
                  let pf' : (i - 1 + 1) - 0 = i := VCGBlock_sorry _;
                  let mret0 := SMT.extract (i - 1) 0 rax;
                  let mret := @Eq.recOn _ _ (fun a _ => SMT.term (SMT.sort.bitvec a)) _ pf' mret0;
                  proveEq lret mret "Return values match"
          else throw "Unexpected return value"
      | _ => throw "Unexpected return value")
  
--------------------------------------------------------------------------------
-- Arithmetic

section
open llvm.value

def arithOpFunc {n : Nat} : llvm.arith_op
                          -> SMT.term (SMT.sort.bitvec n)
                          -> SMT.term (SMT.sort.bitvec n)
                          -> SMT.term (SMT.sort.bitvec n)
| llvm.arith_op.add _ _, x, y => SMT.bvadd x y
| llvm.arith_op.sub _ _, x, y => SMT.bvsub x y
| llvm.arith_op.mul _ _, x, y => SMT.bvmul x y
| _, _, _ =>  SMT.bvimm _ 0 -- FIXME

end

section
open llvm.instruction
  
def stepNextStmt (stmt : llvm.stmt) : BlockVCG Bool := do
  match stmt.instr with
--   | alloca : llvm_type -> Option (typed value) -> Option Nat -> instruction
  | arith aop { type := lty, value := lhs } rhs => do
    if H : HasSMTSort lty then do
      lhsv <- primEval lty H lhs;
      rhsv <- primEval lty H rhs; 
      match asSMTSort lty H, stmt.assign, lhsv, rhsv with
      | _, none, _, _ => pure ()
      | SMT.sort.bitvec n, some i, l, r => defineTerm i (arithOpFunc aop l r) $> ()
      | _, _, _, _ => throw "Unexpected sort";
      pure True
    else throw "Unexpected type"

  | ret v    => llvmReturn (some v) $> false
  | ret_void => llvmReturn none     $> false
  | _ => throw "unimplemented" 
  

--   | bit : bit_op -> typed value -> value -> instruction
--   | conv : conv_op -> typed value -> llvm_type -> instruction
--   | call (tailcall : Bool) : Option llvm_type -> value -> Array (typed value) -> instruction
--   | alloca : llvm_type -> Option (typed value) -> Option Nat -> instruction
--   | load : typed value -> Option atomic_ordering -> Option Nat /- align -/ -> instruction
--   | store : typed value -> typed value -> Option Nat /- align -/ -> instruction
-- /-
--   | fence : option string -> atomic_ordering -> instruction
--   | cmp_xchg (weak : bool) (volatile : bool) : typed value -> typed value -> typed value
--             -> option string -> atomic_ordering -> atomic_ordering -> instruction
--   | atomic_rw (volatile : bool) : atomic_rw_op -> typed value -> typed value
--             -> option string -> atomic_ordering -> instruction
-- -/
--   | icmp : icmp_op -> typed value -> value -> instruction
--   | fcmp : fcmp_op -> typed value -> value -> instruction
--   | phi : llvm_type -> Array (value × block_label) -> instruction
--   | gep (bounds : Bool) : typed value -> Array (typed value) -> instruction
--   | select : typed value -> typed value -> value -> instruction
--   | extract_value : typed value -> List Nat -> instruction
--   | insert_value : typed value -> typed value -> List Nat -> instruction
--   | extract_elt : typed value -> value -> instruction
--   | insert_elt : typed value -> typed value -> value -> instruction
--   | shuffle_vector : typed value -> value -> typed value -> instruction
--   | jump : block_label -> instruction
--   | br : typed value -> block_label -> block_label -> instruction
--   | invoke : llvm_type -> value -> List (typed value) -> block_label -> block_label -> instruction
--   | comment : String -> instruction
--   | unreachable
--   | unwind
--   | va_arg : typed value -> llvm_type -> instruction
--   | indirect_br : typed value -> List block_label -> instruction
--   | switch : typed value -> block_label -> List (Nat × block_label) -> instruction
--   | landing_pad : llvm_type -> Option (typed value) -> Bool -> List (clause × typed value) -> instruction
--   | resume : typed value -> instruction
end

  
--------------------------------------------------------------------------------
-- Runner

namespace BlockVCG

protected 
def run {a : Type}
        (mctx : ModuleVCGContext)
        (funAnn : FunctionAnn)
        (bmap : ReachableBlockAnnMap)
        (firstBlock : llvm.block_label)
        (firstAddr  : Nat) -- FIXME: maybe not strictly required
        (thisBlock  : llvm.block_label)
        (blockAnn   : ReachableBlockAnn)
        (m : BlockVCG Unit) : IO Unit := do
  mctx.proverGen.blockCallback funAnn.llvmFunName thisBlock $ fun prover => do
    let blockStart := blockAnn.startAddr.toNat;
    let sz := blockAnn.codeSize;
    let blockMap : MCBlockAnnMap := 
      (let mk (e : MCMemoryEvent) := (e.addr.toNat, e.info);
       RBMap.ofList (List.map mk blockAnn.memoryEvents.toList));
       
    ((stdLib, blockRegs), nextFree) <- prover.runsmtM 0 (do
      let ann := mctx.annotations;  
      stdLib <- x86.vcg.MCStdLib.make firstAddr ann.pageSize ann.stackGuardPageCount;
      blockRegs <-
        if thisBlock = firstBlock 
        then pure stdLib.funStartRegs
        else x86.vcg.RegState.declare_const blockStart;
      -- FIXME df etc.   
      pure (stdLib, blockRegs));

    let ctx := { BlockVCGContext
               . mcModuleVCGContext := mctx
               , llvmFunName := funAnn.llvmFunName
               , funBlkAnnotations := bmap
               , firstBlockLabel := firstBlock
               , currentBlock    := thisBlock
               , callbackFns     := prover
               , mcBlockEndAddr  := blockStart + sz
               , mcBlockMap      := blockMap
               , mcStdLib        := stdLib
               };
    let s := { BlockVCGState
             . mcCurAddr := blockStart
             , mcCurSize := 0
             , mcCurRegs := blockRegs
             , mcCurMem  := stdLib.blockStartMem
             , mcEvents  := []
             , mcLocalIndex := nextFree
             , llvmInstIndex := 0
             , llvmIdentMap  := RBMap.empty -- FIXME: ???
             };
     r <- ((m.run ctx).run' s).run;
     elseThrowPrefixed r "BlockVCG.run"

end BlockVCG

end ReoptVCG
