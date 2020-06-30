import Galois.Data.RBMap
import Galois.Data.SExp
import SMTLIB.Syntax
import LeanLLVM.AST
import X86Semantics.Common
import ReoptVCG.WordSize

namespace ReoptVCG

section
universes u v


open WellFormedSExp
open SMT

------------------------------------------------------------------------
-- Expression

inductive Atom : Type u
| nat : Nat → Atom
| ident : String → Atom 

def Atom.toString : Atom → String
| Atom.nat n => n.repr
| Atom.ident nm => nm

instance Atom.hasToString : HasToString Atom := ⟨Atom.toString⟩

def readAtom (str : String) : Except String Atom :=
if str.isEmpty
then Except.error "an Atom must contain one or more characters"
else
  match str.toSubstring.toNat? with
  | some n => pure $ Atom.nat n
  | none => pure $ Atom.ident str


def readSExp (str:String) : Except String (SExp Atom) := do
ss ← WellFormedSExp.SExp.readSExps readAtom str;
match ss with
| [] => Except.error "no s-expressions were found in the string"
| [s] => pure s
| _ => Except.error $ "multiple s-expressions were found in the string: " ++ str



/-- An expression in the SMT bitvector theory with 
    variables/constants which may appear in 
    block preconditions. --/
inductive BlockExpr : sort → Type u
| stackHigh : BlockExpr sort.bv64
  -- ^ Denotes the high address on the stack.
  --
  -- This is the address the return address is stored at, and
  -- the curent frame.
| initGPReg64 : x86.reg64 → BlockExpr sort.bv64
  -- ^ Denotes the value of a 64-bit general purpose register
  -- at the start of the block execution.
| fnStartGPReg64 : x86.reg64 → BlockExpr sort.bv64
  -- ^ Denotes the value of a general purpose when the function starts.
  --
  -- Note. We do not support all registers here, only the registers
  -- in `calleeSavedGPRegs`
| mcStack (a : BlockExpr sort.bv64) (w:WordSize) : BlockExpr w.sort
  -- ^ @MCStack a w@ denotes @w@-bit value stored at the address @a@.
  --
  -- The width @w@ should be @8@, @16@, @32@, or @64@.
  --
  -- Our memory model only tracks the mc-only variables, so if the
  -- address is not a stack-only variable, then the value just
  -- means some arbitrary value.
| llvmVar (nm : LLVM.Ident) (tp : sort) : BlockExpr tp
  -- ^ This denotes the value of an LLVM Phi variable when the
  -- block starts.
| eq    {tp : sort} : BlockExpr tp → BlockExpr tp → BlockExpr sort.smt_bool
| bvAdd {n : Nat} : BlockExpr (sort.bitvec n) → BlockExpr (sort.bitvec n) → BlockExpr (sort.bitvec n)
| bvSub {n : Nat} : BlockExpr (sort.bitvec n) → BlockExpr (sort.bitvec n) → BlockExpr (sort.bitvec n)
  -- | @BVDecimal v w@ denotes the @w@-bit value @v@ which should
  -- satisfy the property that @v < 2^w@.
| bvDecimal (v w : Nat) : BlockExpr (sort.bitvec w)

/-- Map from LLVM ident names to their sorts--/
abbrev LLVMTyEnv := RBMap LLVM.Ident SMT.sort (λ x y => x<y)

namespace BlockExpr

private def ppLLVMIdent : LLVM.Ident → String
| LLVM.Ident.named nm => nm
| LLVM.Ident.anon n => n.repr

-- was `evalExpr`
partial def fromSExp
(llvmTyEnv : LLVMTyEnv)
: (SExp Atom) → Except String (Sigma BlockExpr)
| SExp.list [SExp.atom (Atom.ident "="), x, y] => do
  ⟨xtp, xe⟩ ← fromSExp x;
  ⟨ytp, ye⟩ ← fromSExp y;
  if h : (xtp = ytp)
  then 
    let hEq : BlockExpr xtp = BlockExpr ytp := h ▸ rfl;
    Except.ok ⟨sort.smt_bool, eq (cast hEq xe) ye⟩
  else Except.error $ 
       "The two operands in the term `"
       ++ (SExp.list [SExp.atom (Atom.ident "="), x, y]).toString
       ++ "` must have the same type, but the first"
       ++ " was of type " ++ xtp.toString
       ++ " and the second was of type " ++ ytp.toString
| SExp.list [SExp.atom (Atom.ident "bvsub"), x, y] => do
  xRes ← fromSExp x;
  yRes ← fromSExp y;
  match xRes, yRes with
  | ⟨sort.bitvec xw, xe⟩, ⟨sort.bitvec yw, ye⟩ =>
    if h : xw = yw
    then 
      let hEq : BlockExpr (sort.bitvec xw) = BlockExpr (sort.bitvec yw) := h ▸ rfl;
      Except.ok ⟨sort.bitvec yw, bvSub (cast hEq xe) ye⟩
    else Except.error $ 
         "The two operands in the term `"
          ++ (SExp.list [SExp.atom (Atom.ident "bvsub"), x, y]).toString
          ++ "` must both be bitvectors of the same length, but the first"
          ++ " was of length " ++ xw.repr
          ++ " and the second was of length " ++ yw.repr
  | ⟨xtp, xe⟩, ⟨ytp, ye⟩ => 
    Except.error $ "The two operands in the term `"
    ++ (SExp.list [SExp.atom (Atom.ident "bvsub"), x, y]).toString
    ++ "` must both be bitvectors of the same length, but the first"
    ++ " was of type " ++ xtp.toString
    ++ " and the second was of type " ++ ytp.toString
| (SExp.list [SExp.atom (Atom.ident "_"), SExp.atom (Atom.ident bvLit), SExp.atom (Atom.nat width)]) =>
  match bvLit.data with
  | 'b'::'v'::nChars =>
    let nStr := nChars.asString;
    match nStr.toSubstring.toNat? with
    | some n => 
      let val : Nat := Nat.land n $ (Nat.pow 2 width) - 1;
      Except.ok ⟨sort.bitvec width, bvDecimal val width⟩
    | none => Except.error $ "a bitvector literal should have a natural number adjacent to `bv`"
              ++ " but found " ++ bvLit
  | _ => Except.error $ "unrecognized SMT expression: " ++ bvLit
| SExp.list [SExp.atom (Atom.ident "mcstack"), sa, sw] => do
  ⟨tp, a⟩ ← fromSExp sa;
  if h : tp = sort.bv64
  then do
    let hEq : BlockExpr tp = BlockExpr sort.bv64 := h ▸ rfl;
    w ← match sw with
        | SExp.list [SExp.atom (Atom.ident "_"),
                     SExp.atom (Atom.ident "BitVec"),
                     SExp.atom (Atom.nat w)] =>
          match WordSize.fromNat w with
          | some width => Except.ok width
          | none => Except.error "mcstack could not interpret memory type."
        | _ => Except.error "mcstack could not interpret memory type";
    Except.ok ⟨w.sort, BlockExpr.mcStack (cast hEq a) w⟩
  else
    Except.error $ "Expected 64-bit address as first argument to mcstack"
                   ++ " but found a " ++ tp.toString
| SExp.list [SExp.atom (Atom.ident "fnstart"), regExpr] =>
  match regExpr with
  | SExp.atom (Atom.ident regName) =>
    match x86.reg64.fromName regName with
    | some r => Except.ok ⟨sort.bv64, BlockExpr.fnStartGPReg64 r⟩
    | none => Except.error $ "could not interpret register name " ++ regName
  | _ => Except.error $ "could not interpret register name " ++ regExpr.toString
| SExp.list [SExp.atom (Atom.ident "llvm"), llvmExpr] =>
  match llvmExpr with
  | SExp.atom (Atom.ident llvmName) =>
    let nm := LLVM.Ident.named llvmName;
    match llvmTyEnv.find? nm with
    | some tp => Except.ok ⟨tp, BlockExpr.llvmVar nm tp⟩
    | none => Except.error $ "Could not interpret llvm variable " ++ llvmExpr.toString
                           ++ "\nKnown variables: " ++ (llvmTyEnv.keys.map ppLLVMIdent).toString
  | _ => Except.error $ "Could not interpret llvm variable " ++ llvmExpr.toString
                      ++ "\nKnown variables: " ++ (llvmTyEnv.keys.map ppLLVMIdent).toString
| SExp.atom (Atom.ident "stack_high") =>
  Except.ok ⟨sort.bv64, BlockExpr.stackHigh⟩
| SExp.atom (Atom.ident nm) =>
  match x86.reg64.fromName nm with
  | some r => Except.ok ⟨sort.bv64, BlockExpr.initGPReg64 r⟩
  | none => Except.error $ "Could not interpret identifier as a variable: " ++ nm
| sexpr => Except.error $ "Could not interpret expression: " ++ sexpr.toString


-- was simply `fromText` in Haskell, was a moment ago in lean4 `Expr.fromString`
def parseAs
(tp : sort)
(llvmTyEnv : LLVMTyEnv)
(input : String)
: Except String (BlockExpr tp) := do
⟨tp', e⟩ ← readSExp input >>= fromSExp llvmTyEnv;
if h : tp' = tp
then 
  let hEq : BlockExpr tp' = BlockExpr tp := h ▸ rfl;
  Except.ok $ cast hEq e
else Except.error $ "expected " ++ input ++ " to be of type " ++ tp.toString
                  ++ ", but it is of type " ++ tp'.toString


end BlockExpr

end

end ReoptVCG
