import Galois.Data.SExp
import SMTLIB.Syntax

namespace ReoptVCG

universe u

------------------------------------------------------------------------
-- Expression

inductive Atom
| nat : Nat → Atom
| ident : String → Atom 

def readAtom (input : String) : Except String Atom := 
Except.error "TODO: implement readAtom"

abbrev SExpr := WellFormedSExp.SExp Atom

def readSExpr : String → Except String SExpr := 
WellFormedSExp.SExp.read1 readAtom


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

def readExpr {α : Type u} : VarParser α → String → Except String (Expr α) :=
λ varParser input => Except.error "TODO: implement readExpr"


end ReoptVCG
