
import LeanLLVM.AST
import LeanLLVM.LLVMLib
import SMTLIB.Syntax
import ReoptVCG.Types

namespace ReoptVCG

open llvm (llvm_type typed prim_type value)
open SMT (smtM)

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

end BlockVCG

def llvmReturn (mlret : Option (typed value)) : BlockVCG Unit := throw "Not done yet"

-- -- | Convert LLVM type to SMT sort.
-- def asSMTSort : llvm_type -> Option SMT.sort
-- | llvm.llvm_type.ptr_to _  => some (SMT.sort.bitvec 64)
-- | llvm.llvm_type.prim_type (llvm.prim_type.integer i) =>
--   if i > 0 then some (SMT.sort.bitvec i) else none
-- | _ => none

-- structure HasSMTSort (tp : llvm_type) : Prop :=
--    (get : Exists (fun s => asSMTSort tp = some s))

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

-- instance {tp} : Decidable (HasSMTSort tp) :=
--   let v := asSMTSort tp;
--   let contr : v = none -> HasSMTSort tp -> False :=
--     (let nc : forall x, none = some x -> False := fun x h => Option.noConfusion h;
--      fun v_none has => has.casesOn (fun s v_some => nc s (Eq.trans (Eq.symm v_none) v_some)));
  
--   let pf := @Option.casesOn _ (fun x => v = x -> Decidable (HasSMTSort tp)) v
--                               (fun v_none   => isFalse (contr v_none))
--                               (fun x v_some => isTrue (HasSMTSort.intro x v_some));
--   pf rfl

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

-- FIXME: ugh
def mkInt {w : Nat} (v : Int) (H : w > 0)
  : SMT.term (asSMTSort (llvm.llvm_type.prim_type (llvm.prim_type.integer w)) H) :=
  SMT.bvimm' w v

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

def primEval : forall (tp : llvm_type) (H :HasSMTSort tp), value -> BlockVCG (SMT.term (asSMTSort tp H))
| tp, H, ident i => lookupIdent i (asSMTSort tp H)
| llvm.llvm_type.prim_type (llvm.prim_type.integer w), H, integer i => pure (mkInt i H)
| _, _, _ => throw "unimplemented"

-- -- Loses connection with tp, but is probably easier to use.
-- def primEval' (tp : llvm_type) (v : value) : BlockVCG (Sigma SMT.term) := do
--   r <- primEval tp v;
--   @OptionF.casesOn _ _ (fun o_v o_f => BlockVCG (Sigma SMT.term)) _
--                     r (throw ("Couldn't convert a type to SMT ") : BlockVCG (Sigma SMT.term))
--                       (fun v f_v => (pure (Sigma.mk v f_v)       : BlockVCG (Sigma SMT.term)))
--   -- match r with
--   -- | OptionF.someF x => pure (Sigma.mk _ x)
--   -- | OptionF.noneF   => throw ("Couldn't convert a type to SMT ")

end

section
open llvm.instruction

-- def defineTerm {s : SMT.sort) : llvm.ident -> SMT.term s -> BlockVCG Unit :=
  
def stepNextStmt (stmt : llvm.stmt) : BlockVCG Bool := do
  match stmt.instr with
  | ret v    => llvmReturn (some v) $> false
  | ret_void => llvmReturn none     $> false
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
  

end ReoptVCG
