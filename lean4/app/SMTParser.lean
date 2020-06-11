import Galois.Data.SExp
import SMTLIB.Syntax

namespace ReoptVCG

universe u

------------------------------------------------------------------------
-- Expression

inductive Atom
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
  let subStr := str.toSubstring;
  match subStr.toNat? with
  | some n => pure $ Atom.nat n
  | none => pure $ Atom.ident str

abbrev SExpr := WellFormedSExp.SExp Atom

def readSExpr (str:String) : Except String SExpr := do
ss ← WellFormedSExp.SExp.readSExps readAtom str;
match ss with
| [] => Except.error "no s-expressions were found in the string"
| [s] => pure s
| _ => Except.error $ "multiple s-expressions were found in the string: " ++ str


-- TODO / FIXME Should we just use the typed SMT expression AST from the
-- lean SMTLIB? Or is this `Expr` here useful as we just want to reason
-- about a subset or similar?

/-- An expression in the SMT bitvector theory.

   The type `α` allows one to create holes for
   variables or other known constants. --/
inductive Expr (α : Type u)
| eq    : Expr → Expr → Expr
| bvAdd : Expr → Expr → Expr
| bvSub : Expr → Expr → Expr
  -- | @BVDecimal v w@ denotes the @w@-bit value @v@ which should
  -- satisfy the property that @v < s^w@.
| bvDecimal : Nat -> Nat -> Expr
| atom : α -> Expr

def VarParser (α : Type u) := SExpr -> Except String (α × SMT.sort)

-- was simply `fromText` in Haskell
def Expr.fromString
{α : Type u}
(varParser : VarParser α)
(input : String) : Except String (Expr α) :=
Except.error "TODO: implement Expr.fromString"

def evalExpr {α : Type u} : VarParser α → SExpr → Except String ((Expr α) × SMT.sort) :=
λ varParser input => Except.error "TODO: implement readExpr"


end ReoptVCG
