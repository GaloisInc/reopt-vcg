import Galois.Data.RBMap
import Galois.Data.SExp
import SmtLib.Smt
import LeanLLVM.AST
import X86Semantics.Common
import ReoptVCG.WordSize

import ReoptVCG.SExpParser

open Std (RBMap)

namespace ReoptVCG

section
universes u v

open WellFormedSExp
open Smt

------------------------------------------------------------------------
-- Expression

inductive Atom : Type u
| nat : Nat → Atom
| ident : String → Atom 
  deriving DecidableEq

def Atom.toString : Atom → String
| Atom.nat n => n.repr
| Atom.ident nm => nm

instance Atom.hasToString : ToString Atom := ⟨Atom.toString⟩

def readAtom (str : String) : Except String Atom :=
if str.isEmpty
then Except.error "an Atom must contain one or more characters"
else
  match str.toSubstring.toNat? with
  | some n => pure $ Atom.nat n
  | none => pure $ Atom.ident str


def readSExp (str:String) : Except String (SExp Atom) := do
  let ss ← WellFormedSExp.SExp.readSExps readAtom str
  match ss with
  | [] => Except.error "no s-expressions were found in the string"
  | [s] => pure s
  | _ => Except.error $ "multiple s-expressions were found in the string: " ++ str

/- An expression in the SMT bitvector theory with 
    variables/constants which may appear in 
    block preconditions. -/
inductive BlockExpr : SmtSort → Type u
| stackHigh : BlockExpr SmtSort.bv64
  -- ^ Denotes the high address on the stack.
  --
  -- This is the address the return address is stored at, and
  -- the curent frame.
| initGPReg64 : x86.reg64 → BlockExpr SmtSort.bv64

| initFlag : x86.flag -> BlockExpr SmtSort.bool

  -- ^ Denotes the value of a 64-bit general purpose register
  -- at the start of the block execution.
| fnStartGPReg64 : x86.reg64 → BlockExpr SmtSort.bv64
  -- ^ Denotes the value of a general purpose when the function starts.
  --
  -- Note. We do not support all registers here, only the registers
  -- in `calleeSavedGPRegs`

| beforeCallGPReg64 : x86.reg64 → BlockExpr SmtSort.bv64
  -- ^ Used to refer to the value of a register before a function call
  -- (used for function post conditions)

| mcStack (a : BlockExpr SmtSort.bv64) (w:WordSize) : BlockExpr w.sort
  -- ^ @MCStack a w@ denotes @w@-bit value stored at the address @a@.
  --
  -- The width @w@ should be @8@, @16@, @32@, or @64@.
  --
  -- Our memory model only tracks the mc-only variables, so if the
  -- address is not a stack-only variable, then the value just
  -- means some arbitrary value.
| llvmVar (nm : LLVM.Ident) (tp : SmtSort) : BlockExpr tp
  -- ^ This denotes the value of an LLVM Phi variable when the
  -- block starts.

-- A bit gross, but this allows us a bit more flexibility 
| smtBinOp {tp tp' tp'' : SmtSort} : Smt.Raw.BuiltinIdent (Smt.Raw.BuiltinIdent.binop tp tp' tp'') -> 
           BlockExpr tp → BlockExpr tp' → BlockExpr tp''

-- | smtUnOp {tp tp' : SmtSort} : Smt.Raw.BuiltinIdent (Smt.Raw.BuiltinIdent.unop tp tp') -> 
--            BlockExpr tp → BlockExpr tp'

| smtBool : Bool -> BlockExpr SmtSort.bool

  -- | @BVDecimal v w@ denotes the @w@-bit value @v@ which should
  -- satisfy the property that @v < 2^w@.
| bvDecimal (v w : Nat) : BlockExpr (SmtSort.bitvec w)


/- Map from LLVM ident names to their sorts -/
abbrev LLVMTyEnv := RBMap LLVM.Ident SmtSort (λ x y => x<y)

end

namespace BlockExpr

open Smt (SmtSort)
open WellFormedSExp (SExp)

private def ppLLVMIdent : LLVM.Ident → String
| LLVM.Ident.named nm => nm
| LLVM.Ident.anon n => n.repr

-- private def binop {tp tp' tp'' : SmtSort} (ident : Smt.Raw.BuiltinIdent (Smt.Raw.BuiltinIdent.binop tp tp tp')) 
--                   (e1 : BlockExpr tp) (e2 : BlockExpr tp') : BlockExpr tp'' :=
--   smtBinOp ident e1 e2

section

open Smt.Raw (BuiltinIdent)
open Smt.Raw.BuiltinIdent
open SExpParser

private def identP : SExpParser Atom String := do
  let a <- atom
  match a with 
  | Atom.ident i => pure i
  | _ => throw ()

private def natP : SExpParser Atom Nat := do
  let a <- atom
  match a with 
  | Atom.nat n => pure n
  | _ => throw ()

private def exactIdentP (s : String) := exact (Atom.ident s)

instance : Inhabited (Sigma BlockExpr) := { default := Sigma.mk _ stackHigh }

private def gprP : SExpParser Atom x86.reg64 := do
  let nm <- identP
  match x86.reg64.fromName nm with
  | some r  => pure r
  | none    => throw ()

private def flagP : SExpParser Atom x86.flag := do
  let nm <- identP
  match x86.flag.fromName nm with
  | some r  => pure r
  | none    => throw ()
  

private def bvLitP : SExpParser Atom (Sigma BlockExpr) := list $ do
  exactIdentP "_"
  let bvLit <- identP
  let width <- natP
  match bvLit.data with
  | 'b'::'v'::nChars =>
    let nStr := nChars.asString;
    match nStr.toSubstring.toNat? with
    | some n => 
      let val : Nat := Nat.land n $ (Nat.pow 2 width) - 1;
      pure (Sigma.mk _ $ bvDecimal val width)
    | none => throw ()
  | _ => throw ()

private def llvmVarP (llvmTyEnv : LLVMTyEnv)
  : SExpParser Atom (Sigma BlockExpr) := list $ do
  exactIdentP "llvm"
  let llvmName <- identP
  let nm := LLVM.Ident.named llvmName
  match llvmTyEnv.find? nm with
  | some tp => pure (Sigma.mk _ $ BlockExpr.llvmVar nm tp)
  | _ => throw ()

partial
def parser (llvmTyEnv : LLVMTyEnv) : SExpParser Atom (Sigma BlockExpr) := do
  let go := parser llvmTyEnv

  let checked : forall tp, SExpParser Atom (BlockExpr tp) := fun tp => do
      let ⟨tp', e⟩ <- parser llvmTyEnv -- go
      if h : tp' = tp
      then 
        let hEq : BlockExpr tp' = BlockExpr tp := h ▸ rfl;
        pure (cast hEq e)
      else throw ()
  
  let mkBvBinOp (tp) (op : forall n, BuiltinIdent (binop (SmtSort.bitvec n) (SmtSort.bitvec n) (tp n)))
              (i : String) :=
      list (do exactIdentP i;
               let xRes ← go
               let yRes ← go
               match xRes, yRes with
               | ⟨SmtSort.bitvec xw, xe⟩, ⟨SmtSort.bitvec yw, ye⟩ =>
                 if h : xw = yw
                 then 
                   let hEq : BlockExpr (SmtSort.bitvec xw) = BlockExpr (SmtSort.bitvec yw) := h ▸ rfl;
                   pure (Sigma.mk _ (smtBinOp (op yw) (cast hEq xe) ye))
                 else throw ()
               | _, _ => throw ())
  let bvBinOp  := mkBvBinOp SmtSort.bitvec
  let bvBoolOp := mkBvBinOp (fun _ => SmtSort.bool)

  -- Binary version, n-ary causes an infinite loop :/
  let mkLAssocBoolOp (op : BuiltinIdent (binop SmtSort.bool SmtSort.bool SmtSort.bool)) (i : String) :=
      list (do exactIdentP i; 
               let tm <- smtBinOp op <$> checked _ <*> checked _;
               pure (Sigma.mk _ tm))

  let mkRAssocBoolOp := mkLAssocBoolOp

  -- let mkLAssocBoolOp (op : BuiltinIdent (binop SmtSort.bool SmtSort.bool SmtSort.bool)) (i : String) :=
  --     list (do exactIdentP i; 
  --              let hd <- checked SmtSort.bool;
  --              let rest <- many (checked SmtSort.bool);
  --              pure (Sigma.mk _ (List.foldl (smtBinOp op) hd rest)))

  -- let mkRAssocBoolOp (op : BuiltinIdent (binop SmtSort.bool SmtSort.bool SmtSort.bool)) (i : String) :=
  --     list (do exactIdentP i; 
  --              let els <- many1 (checked SmtSort.bool);
  --              match List.rotateRight els with
  --              | [] => throw ()
  --              | x :: rest => pure (Sigma.mk _ (List.foldr (smtBinOp op) x rest)))

  let eqOp := list (do 
      exactIdentP "="
      let ⟨xtp, xe⟩ ← go
      let ⟨ytp, ye⟩ ← go
      if h : (xtp = ytp)
      then 
        let hEq : BlockExpr xtp = BlockExpr ytp := h ▸ rfl
        pure ⟨SmtSort.bool, smtBinOp (eq ytp) (cast hEq xe) ye⟩
      else throw ())

  let initReg := 
    first [ (fun r => Sigma.mk _ (BlockExpr.initGPReg64 r)) <$> gprP
          , (fun r => Sigma.mk _ (BlockExpr.initFlag    r)) <$> flagP
          ]

  let mcstackP := list $ do
    exactIdentP "mcstack"    
    let ⟨tp, a⟩ ← go
    if h : tp = SmtSort.bv64
    then do
      let hEq : BlockExpr tp = BlockExpr SmtSort.bv64 := h ▸ rfl;
      let w <- list $ do
        exactIdentP "_"
        exactIdentP "BitVec"
        let w <- natP
        match WordSize.fromNat w with
        | some width => pure width        
        | none       => throw ()
      pure (Sigma.mk _ $ BlockExpr.mcStack (cast hEq a) w)
    else throw ()

  first [ eqOp
        , bvBoolOp bvslt "bvslt" 
        , bvBoolOp bvult "bvult" 
        , bvBoolOp bvsle "bvsle" 
        , bvBoolOp bvule "bvule" 
        , bvBinOp  bvadd "bvadd"
        , bvBinOp  bvsub "bvsub"
        , mkLAssocBoolOp or "or"
        , mkLAssocBoolOp and "and"
        , mkRAssocBoolOp impl "=>"
        , do exactIdentP "stack_high"; pure (Sigma.mk _ stackHigh)
        , bvLitP
        , initReg
        , llvmVarP llvmTyEnv
        , mcstackP
        , exactIdentP "true" *> pure (Sigma.mk _ (BlockExpr.smtBool true))
        , exactIdentP "false" *> pure (Sigma.mk _ (BlockExpr.smtBool false))
        , list (do exactIdentP "fnstart"; 
                   let r <- gprP
                   pure (Sigma.mk _ (BlockExpr.fnStartGPReg64 r)))
        , list (do exactIdentP "before_call"; 
                   let r <- gprP
                   pure (Sigma.mk _ (BlockExpr.beforeCallGPReg64 r)))
        ]

partial def fromSExp
  (llvmTyEnv : LLVMTyEnv)
  (input : String) : Except String (Sigma BlockExpr) := do
  let sexp <- readSExp input 
  match runSExpParser (parser llvmTyEnv) [sexp] with
  | some (r, []) => Except.ok r
  | _            => Except.error ("parse failed for " ++ input)

end

-- was simply `fromText` in Haskell, was a moment ago in lean4 `Expr.fromString`
def parseAs
(tp : SmtSort)
(llvmTyEnv : LLVMTyEnv)
(input : String)
: Except String (BlockExpr tp) := do
  let ⟨tp', e⟩ <- fromSExp llvmTyEnv input;
  if h : tp' = tp
  then 
    let hEq : BlockExpr tp' = BlockExpr tp := h ▸ rfl;
    Except.ok $ cast hEq e
  else Except.error $ "expected " ++ input ++ " to be of type " ++ tp.toString
                    ++ ", but it is of type " ++ tp'.toString

-- #eval (match readSExp "(= rbx (fnstart rbx))" >>= fromSExp RBMap.empty with | Except.ok _ => "ok" | _ => "not ok")

end BlockExpr

end ReoptVCG
