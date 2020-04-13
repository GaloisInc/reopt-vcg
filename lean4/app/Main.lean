import Init.System.IO
import Init.Data.RBMap
import Init.Data.PersistentHashMap
import Init.Control.Functor
import Init.Control.Reader

-- import X86Semantics.MachineMemory

-- WIP, mimicing behavior from :
-- https://github.com/GaloisInc/reopt/blob/master/reopt-vcg/app/Main.hs


------------------------------------------------------
-- FIXME -- stub definitions
------------------------------------------------------


def ByteString := List UInt8
instance ByteString.HasLess : HasLess ByteString := List.HasLess

def ByteString.fromString (s:String) : ByteString := [] -- FIXME

-- Macaw types and similar
def Ty := Unit -- FIXME --  was just `Type` from Macaw.CFG
def Ty.toString (_:Ty) : String := "TODO(Ty.toString)"
instance Ty.HasToString : HasToString Ty := ⟨Ty.toString⟩



section
variable (n:Nat)

def MemSegmentOff := Fin n -- FIXME bitvec?
def Memory := Fin n -- FIXME
def MemWord := Fin n -- FIXME

def MemWord.toString {n} (w:MemWord n) : String := w.val.repr -- FIXME
instance MemWord.HasToString : HasToString (MemWord n) := ⟨MemWord.toString⟩
def MemWord.toHex {n} (w:MemWord n) : String := w.toString -- FIXME


structure MemAddr := (base : MemWord n) (offset : MemWord n) -- FIXME
end -- section

def X86Reg (α : Ty) := Unit -- FIXME
def X86Reg.toString {tp} (reg : X86Reg tp) : String := "reg" -- FIXME

def RegState (k : Ty -> Type) (v : Ty -> Type) := Unit -- FIXME
def Event := Unit -- FIXME

def LocalIdent := String -- FIXME
instance LocalIdent.HasLess : HasLess LocalIdent := inferInstanceAs (HasLess String)

def Allocation.Annotation := Unit -- FIXME

def Memory.Annotation := Unit -- FIXME

section
variable {n:Nat}

def MemSegmentOff.toString (w:MemWord n) : String := w.val.repr -- FIXME...?
instance MemSegmentOff.HasToString : HasToString (MemSegmentOff n) := ⟨λ x => x.val.repr⟩
instance MemSegmentOff.HasLess : HasLess (MemSegmentOff n) := inferInstanceAs (HasLess (Fin n))

def MemSegmentOff.asAbsoluteAddr {n} (mso:MemSegmentOff n) : Option (MemWord n) := some mso -- FIXME



end -- section



def Ident := String -- FIXME...?
def Ident.toString (x:Ident) : String := x
instance Ident.HasToString : HasToString Ident := ⟨Ident.toString⟩


-- Module
namespace Module
def Annotation := Unit -- FIXME
end Module

-- Block
namespace Block

def Annotation := Unit -- FIXME

def Label := String -- FIXME
def Label.toString (l:Label) : String := l
instance Label.HasToString : HasToString Label := ⟨Label.toString⟩
instance Label.HasLess : HasLess Label := String.HasLess

end Block
-- end Block

-- LLVM
namespace LLVM

def Ident := String -- FIXME
def Ident.toString (x:Ident) : String := x
instance Ident.HasToString : HasToString Ident := ⟨Ident.toString⟩
instance Ident.HasLess : HasLess Ident := String.HasLess

def Ty := Unit
def Ty.toString (t:Ty) : String := "Ty"
instance Ty.HasToString : HasToString Ty := ⟨Ty.toString⟩


def Stmt := Unit -- FIXME

def Stmt.toString : Stmt → String := λ _ => "stmt"

def Value := Unit -- FIXME


end LLVM
-- end LLVM

def Builder := String -- was Data.Text.Lazy.Builder
-- perhaps copy and modify `lean4/tests/playground/lazylist.lean` to build a lazy string or similar if needed?
instance Builder.HasAppend : HasAppend Builder := String.HasAppend

namespace SMT
structure Command := (content : Builder) -- FIXME?

@[reducible] def Term := Builder

def assert (t : SMT.Term) : SMT.Term := t
def eq (ts : List SMT.Term) : SMT.Term := "eq("++(String.intercalate ", " ts)++")"
def distinct (ts : List SMT.Term) : SMT.Term := "neq("++(String.intercalate ", " ts)++")"

instance Term.ToCommand : HasCoe Term Command := ⟨λ t => {content := t}⟩

def Ty := Unit -- FIXME

def declareFun (nm : String) (args : List Term) (retTy : Ty) : SMT.Command :=
  ⟨"(declare_fn "++nm++"_"⟩ -- FIXME
def defineFun (nm : String) (args : List Term) (retTy : Ty) (body : SMT.Term) : SMT.Command := 
  ⟨"(define_fn "++nm++"_"⟩ -- FIXME

end SMT

def toSMTSort (ty : Ty) : Ty := ty -- FIXME

def varTerm (nm:String) : SMT.Term := nm

def Const (α : Type) (β : Ty) := Unit -- FIXME
def Const.mk {α β} (a : SMT.Term) : Const α β := ()


def mkRegStateM {tp : Ty} (f: (X86Reg tp) → IO (Const SMT.Term tp)) : IO (RegState X86Reg (Const SMT.Term)) := 
  pure ()


instance Sigma.x86RegHasLess : HasLess (Sigma X86Reg) := ⟨λ x y => true⟩ -- FIXME lol



------------------------------------------------------
-- ENDOF FIXME -- stub definitions
------------------------------------------------------




-- Maps phi variable names to their corresponding type and values
-- for each source block.
def PhiVarMap := PHashMap String (Ty × (RBMap Block.Label LLVM.Value (λ x y => x < y)))

-- Information about a block including annotations
structure AnnotatedBlock :=
  (annotation : Block.Annotation) 
  (label : Block.Label)
    -- ^ Label for block
  (phiVarMap : PhiVarMap)
  (statements : List LLVM.Stmt)
    -- ^ Statements after phi variables.



-- Maps LLM block labels to their associated annotations.
def ReachableBlockAnnMap := PHashMap String AnnotatedBlock

-- Find a block with the given label in the config.
def findBlock (m:ReachableBlockAnnMap) : Block.Label → Option (Block.Annotation × PhiVarMap)
| lbl => do
  ab <- m.find? lbl;
  pure (ab.annotation, ab.phiVarMap)


def SMT.comment (b:Builder) : SMT.Command := ⟨"; " ++ b⟩


structure ProverInterface :=
  (addCommandCallback : SMT.Command -> IO Unit)
    -- ^ Invoked to add an SMT command.
    --
    -- These commands must not change the solver out of assert mode.
  (proveFalseCallback : SMT.Term -> String -> IO Unit)
    -- ^ Invoked when we have a proposition to prove is false for all
    -- interprettions.
    --
    -- The message is provide so the user knows the source of the
    -- check.
  (proveTrueCallback : SMT.Term -> String -> IO Unit)
    -- ^ Invoked when we have a proposition to prove is true for all
    -- interpretations.
    --
    -- The message is provide so the user knows the source of the
    -- check.
  (blockErrorCallback : Int -> MemSegmentOff 64 -> String -> IO Unit)



-- Lean uses the `Function` namespace
namespace Fn

-- The name of a function in the annotation.
--
-- This is the name in LLVM.
def Name := String

-- Errors that are tied to a specific function.
inductive Error
| NotFound : Error
| ArgTypeUnsupported : Ident -> LLVM.Ty -> Error
| MissingEntryBlock : Error
| EntryUnreachable : Error
| Custom : String -> Error


namespace Error

instance : HasCoe String Error := ⟨Error.Custom⟩

def toString : Error → String
| NotFound => "Could not find definition in LLVM."
| ArgTypeUnsupported x t => "Function argument "++x.toString++"has unsupported type "++t.toString++"."
| MissingEntryBlock => "Function body is missing an entry block."
| EntryUnreachable => "Function entry marked unreachable."
| Custom msg  => msg

instance : HasToString Error := ⟨toString⟩

end Error

end Fn





-- Function for creating sessions to interact with SMT solver.
--
-- As blocks can be independently verified, we create a separate
-- prover interface for each block to be verified.
structure ProverSessionGenerator :=
  (blockCallbacks  : Fn.Name -> Block.Label -> (ProverInterface -> IO Unit) -> IO Unit)
  (sessionComplete : IO Unit)


structure ModuleVCG.Context :=
  (moduleAnn : Module.Annotation)
  -- ^ Annotations for module.
  (moduleMem : Memory 64)
  -- ^ Machine code memory
  (symbolAddrMap : RBMap ByteString (MemSegmentOff 64) (λ x y => x < y))
  -- ^ Maps bytes to the symbol name
  (writeStderr : Bool)
  -- ^ Controls whether logs, warnings or errors
  -- chould be written to stderr.
  --
  -- If false, the messages are droped, but warning
  -- count is increased.
  (errorCount : IO.Ref Nat)
  -- ^ Counts numbers of warnings generated during
  -- verification for display at end of run.
  (proverGen : ProverSessionGenerator)
  -- ^ Interface for generating prover sessions.
  (moduleTypeMap : (RBMap LLVM.Ident LLVM.Ty (λ x y => x < y)))
  -- ^ type map for module.



namespace Block

inductive Error
| AnnParseFailure : String → Error
| MissingAnnotations : Error
| UnsupportedPhiVarType : Ident → Ty → Error
| BlockAddrInvalid : MemWord 64 → Error

namespace Error

def toString : Error → String
| AnnParseFailure msg => "Annotation parse failure: " ++ msg
| MissingAnnotations => "Could not find block annotations."
| UnsupportedPhiVarType x t => "Phi variable "++x.toString++" has unsupported type "++t.toString++"."
| BlockAddrInvalid addr => "Annotated block address "++addr.toString++" is not not in code segment."

end Error

end Block




namespace Module

inductive Error
| Custom : String → Error
| Function : Fn.Name → Fn.Error → Error
| Block : Fn.Name → Block.Label → Block.Error → Error
| IO : IO.Error -> Error

namespace Error

def toString : Error → String
| Custom msg => msg
| Function fnm ferr => fnm++". "++ferr.toString
| Block fnm lbl err => fnm++"."++lbl.toString++". "++err.toString
| IO err => err.toString

def toIOError : Error → IO.Error
| Error.IO ioErr => ioErr
| e => IO.userError $ "Uncaught module VCG error: " ++ e.toString


def liftIO {α} (m : EIO IO.Error α) : EIO Error α := 
  m.adaptExcept Error.IO


instance : MonadIO (EIO Error) := {monadLift := @liftIO}


end Error

end Module


-- Pretty print an error that occurs at the start of an instruction.
def renderMCInstError
 (fnm  : Fn.Name) -- ^ Name of function
 (lbl  : Block.Label) -- ^ Block label
 (idx  : Int) -- ^ LLVM instruction index
 (addr : MemSegmentOff 64) -- ^ Address of current instruction.
 (msg  : String) -- ^ Message
 : String :=
  fnm++"."++lbl.toString++"."++idx.repr++" ("++addr.toString++"). "++msg
  -- ^^ FIXME `addr.toString` here was `showsPrec 10 addr ""`... does that matter?




-------------------------------------------------------
-- ModuleVCG
-------------------------------------------------------


-- A monad for running verification of an entire module
@[reducible]
def ModuleVCG := ReaderT ModuleVCG.Context (EIO Module.Error)

namespace ModuleVCG
instance : Functor ModuleVCG := 
  inferInstanceAs (Functor (ReaderT ModuleVCG.Context (EIO Module.Error)))
instance : Applicative ModuleVCG :=
  inferInstanceAs (Applicative (ReaderT ModuleVCG.Context (EIO Module.Error)))
instance : Monad ModuleVCG :=
  inferInstanceAs (Monad (ReaderT ModuleVCG.Context (EIO Module.Error)))

-- Run "standard" IO by wrapping any exceptions thrown in our Module.Error.IO wrapper.
def liftIO {α} (m : IO α) : ModuleVCG α := 
  monadLift $ m.adaptExcept Module.Error.IO

instance ModuleVCG.MonadIO : MonadIO ModuleVCG := {monadLift := @liftIO}
instance : MonadReader ModuleVCG.Context ModuleVCG :=
  inferInstanceAs (MonadReader ModuleVCG.Context (ReaderT ModuleVCG.Context (EIO Module.Error)))
end ModuleVCG


def runModuleVCG (ctx : ModuleVCG.Context) (m : ModuleVCG Unit) : IO Unit := 
  EIO.adaptExcept Module.Error.toIOError (m.run ctx) 

def vcgLog (msg : String) : ModuleVCG Unit := do 
  ctx ← read;
  when ctx.writeStderr $ 
    IO.println msg -- FIXME can't find the handle for stderr =\

-- A warning that stops execution until catch.
def functionError {α} (fnm : Fn.Name) (e : Fn.Error) : ModuleVCG α :=
  throw $ Module.Error.Function fnm e

-- A warning that stops execution until catch.
def blockError {α} (fnm : Fn.Name) (lbl : Block.Label) (e : Block.Error) : ModuleVCG α :=
  throw $ Module.Error.Block fnm lbl e

-- A warning that stops execution until catch.
def moduleThrow {α} (errMsg : String) : ModuleVCG α :=
  throw $ Module.Error.Custom errMsg


-- Catch a VCG error, print it to the screen and keep going.
def moduleCatch (m : ModuleVCG Unit) :  ModuleVCG Unit :=
  λ ctx => do
    catch (m.run ctx) $ λ (e : Module.Error) =>
      when ctx.writeStderr $
        IO.println $ "Error: " ++ e.toString; -- FIXME use stderr
      ctx.errorCount.modify (λ n => n+ 1)




-------------------------------------------------------
-- BlockVCG
-------------------------------------------------------


namespace BlockVCG

-- Information that does not change during execution of a BlockVCG action.
structure Context :=
  (mcModuleVCGContext : ModuleVCG.Context)
    -- ^ Information at module level about CFG.
  (llvmFunName : String)
    -- ^ Annotations for the current function.
  (funBlkAnnotations : ReachableBlockAnnMap)
    -- ^ Annotations for blocks in the CFG.
  (firstBlockLabel : Block.Label)
    -- ^ Label for first block in this function
  (currentBlock : Block.Label)
    -- ^ Label for block we are verifying.
  (callbackFns : ProverInterface)
    -- ^ Functions for interacting with SMT solver.
  (mcBlockEndAddr : MemAddr 64)
    -- ^ The end address of the block.
  (mcBlockMap : RBMap (MemSegmentOff 64) Memory.Annotation (λ x y => x < y))
    -- ^ Map from addresses to annotations of events on that address.

-- State that changes during execution of a BlockVCG action.
structure State :=
  (mcCurAddr : MemSegmentOff 64)
    -- ^ Address of the current instruction
  (mcCurSize : MemWord 64)
    -- ^ Size of current instruction.
  (mcX87Top : Int)
    -- ^ Top index in x86 stack (starts at 7 and grows down).
  (mcDF : Bool)
    -- ^ Direction flag
  (mcCurRegs : RegState X86Reg (Const SMT.Term))
    -- ^ Map registers to the SMT term.
  (mcMemIndex : Nat)
    -- ^ Index of last defined memory object.
  (mcEvents : List Event)
    -- ^ Unprocessed events from last instruction.
  (mcLocalIndex : Int)
    -- ^ Index of next local variable for machine code.
  (mcPendingAllocaOffsetMap : RBMap LocalIdent Allocation.Annotation (λ x y => x < y))
    -- ^ This is a map from allocation names to the annotations about their
    -- size and offset.
  (llvmInstIndex : Int)
    -- ^ Index of next LLVM instruction within block to execute
    -- Used for error reporting
  (activeAllocaSet : RBTree LocalIdent (λ x y => x < y))
    -- ^ Set of allocation names that are active.

end BlockVCG

-- A Monad for verifying an individual block.
def BlockVCG (α : Type) : Type :=
  BlockVCG.Context
  → (α → BlockVCG.State -> IO Unit)
  → BlockVCG.State
  → IO Unit

namespace BlockVCG

instance : Functor BlockVCG :=
  {map := λ _ _ f g => λ ctx c => g ctx (c ∘ f)}
instance : HasPure BlockVCG :=
  {pure := λ _ x => λ _ c s => c x s }
instance : HasSeq BlockVCG :=
  {seq := λ _ _ mf mx => λ ctx c s0 => mf ctx (λ f s1 => mx ctx (λ x s2 => c (f x) s2) s1) s0}
instance : HasBind BlockVCG := 
  {bind := λ _ _ ma mf => λ ctx c s0 => ma ctx (λ a s1 => (mf a) ctx c s1) s0}
instance : MonadReader Context BlockVCG := 
  {read := λ ctx c s => c ctx s}

def get : BlockVCG State := λ _ c s => c s s
def set (s : State) : BlockVCG PUnit := λ _ c _ => c Unit.unit s
def modifyGet {α} (f : State → (α × State)) : BlockVCG α :=
do
  s ← BlockVCG.get;
  let (a,s) := f s;
  BlockVCG.set s;
  pure a

instance : MonadState State BlockVCG :=
  { get := BlockVCG.get
  , set := BlockVCG.set
  , modifyGet := @BlockVCG.modifyGet
  }

instance : MonadIO BlockVCG := 
  {monadLift := λ _ m => λ ctx c s => do a ← m; c a s}


end BlockVCG


-- Stop verifying the block.
def haltBlock {α} : BlockVCG α := λ _ _ _ => pure ()

-- | This prepends the LLVM and machine code location information for
-- display to user.
def prependLocation (msg : String) : BlockVCG String :=
do
  thisFun ← BlockVCG.Context.llvmFunName <$> read;
  thisBlk ← BlockVCG.Context.currentBlock <$> read;
  thisInst ← BlockVCG.State.llvmInstIndex <$> get;
  addr ← BlockVCG.State.mcCurAddr <$> get;
  pure $ renderMCInstError thisFun thisBlk thisInst addr msg


-- | Report an error at the given location and stop verification of
-- this block.
def fatalBlockError {α} (msg : String) : BlockVCG α := 
do
  thisInst ← BlockVCG.State.llvmInstIndex <$> get;
  addr ← BlockVCG.State.mcCurAddr <$> get;
  prover ← BlockVCG.Context.callbackFns <$> read;
  let callback := ProverInterface.blockErrorCallback prover;
  monadLift $ callback thisInst addr msg;
  haltBlock


def addCommand (cmd : SMT.Command) : BlockVCG Unit :=
do
  prover ← BlockVCG.Context.callbackFns <$> read;
  monadLift $ ProverInterface.addCommandCallback prover cmd



-- Add assertion that the propositon is true without requiring it to be proven.
def addAssert (p : SMT.Term) : BlockVCG Unit := addCommand $ SMT.assert p


-- @proveTrue p msg adds a proof obligation @p@ is true for all
-- interpretations of constants with the message @msg@.
def proveTrue (p : SMT.Term) (msg : String) : BlockVCG Unit :=
do
  annMsg ← prependLocation msg;
  fns ← BlockVCG.Context.callbackFns <$> read;
  monadLift $ ProverInterface.proveTrueCallback fns p annMsg;
  addAssert p


-- @proveEq x y msg@ add a proof obligation named @msg@ asserting
-- that @x@ equals @y@.
def proveEq (x y : SMT.Term) (msg : String) : BlockVCG Unit :=
do
  fns ← BlockVCG.Context.callbackFns <$> read;
  annMsg <- prependLocation msg;
  monadLift $ ProverInterface.proveFalseCallback fns (SMT.distinct [x,y]) annMsg;
  -- Add command for future proofs
  addAssert (SMT.eq [x,y])


-- | This records the current LLVM statement for pretty-printing purposes
def setCurrentLLVMStmt (s : LLVM.Stmt) : BlockVCG Unit :=
  addCommand $ SMT.comment ("LLVM: "++ s.toString)
  -- FIXME? was `"LLVM: " <> fromString (show (L.ppLLVM38 (L.ppStmt stmt))))`

-- | Use a map from symbol names to address to find address.
def getMCAddrOfLLVMFunction
  (m : RBMap ByteString (MemSegmentOff 64) (λ x y => x < y))
  -- ^ Map from symbol names in machine code
  -- to the address in the binary.
  (nm : String)
  : Sum String (MemWord 64) :=
  let llvmFun := ByteString.fromString nm;
  match m.find? llvmFun with
  | none => Sum.inl $ "Cannot find address of LLVM symbol: " ++ nm
  | some expectedAddr =>
      match expectedAddr.asAbsoluteAddr with
      | some addr => Sum.inr addr
      | none => Sum.inl $ "Could not resolve concrete address for " ++ nm


-- | Denotes the "name" of an address for pretty printing purposes.
@[reducible] def AddrName := String

-- | Return the name for SMTLIB display purposes of an address.
def addrName {w} (addr : MemAddr w) : AddrName :=
  let base := addr.base.toString;
  let off := addr.offset.toHex;
  if addr.base.val = 0
  then "a"++off
  else "r"++base++"_"++off

-- | Return the name of the SMT variable for the register at the
-- given PC.
def addrStartRegValue {tp} (b : AddrName) (reg : X86Reg tp) : String :=
  b ++ "_" ++ reg.toString




-- BOOKMARK TODO / FIXME / PICK UP HERE

-- | Declare an SMT value for each register that defines the value of
-- the register when the function at the given address starts
-- execution.
-- def declareAddrStartRegValues
--  (prover : ProverInterface)
--  (nm : AddrName)
--  (definedRegMap : RBMap (Sigma X86Reg) SMT.Term (λ x y => x < y))
--  : IO (RegState X86Reg (Const SMT.Term)) :=
-- do
--   let initReg : ∀ {tp : Ty}, X86Reg tp → IO (Const SMT.Term tp) :=
--       (λ tp reg =>
--         do 
--           let regName := addrStartRegValue nm reg;
--           match definedRegMap.find? (Sigma.mk tp reg) with
--           | none => do
--             let fn :=  SMT.declareFun regName  [] $ toSMTSort tp;
--             ProverInterface.addCommandCallback prover fn;
--             pure $ Const.mk (varTerm regName)
--           | some t => do
--             let fn := SMT.defineFun regName  [] (toSMTSort tp) t;
--             ProverInterface.addCommandCallback prover fn;
--             pure $ Const.mk (varTerm regName));
--   mkRegStateM initReg


------------------------------------------------------
-- Main
------------------------------------------------------


def showHelp : IO Unit := do
  IO.println
    $  "reopt-vcg generates verification conditions to prove that reopt generated\n"
    ++ "   LLVM is faithful to the input binary.\n"
    ++ "Usage: reopt-vcg <input.yaml> {--export <export-dir> | --solver <solver-path>}"

def main (args:List String) : IO UInt32 := do
  showHelp;
  pure 0




