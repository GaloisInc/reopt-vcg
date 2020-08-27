import Galois.Data.SExp


abbrev SExpr := WellFormedSExp.SExp String

namespace SExpr

open WellFormedSExp
open WellFormedSExp.SExp

class HasToSExpr (a : Type) := (toSExpr : a -> SExpr)

open HasToSExpr

instance SExpr.HasToSExpr : HasToSExpr SExpr := ⟨id⟩

def List.toSExpr {a : Type} [HasToSExpr a] (ss : List a) : SExpr :=
list $ ss.map HasToSExpr.toSExpr

instance List.HasToSExpr {a : Type} [HasToSExpr a] : HasToSExpr (List a) :=
⟨List.toSExpr⟩

def Nat.toSExpr : Nat → SExpr := atom ∘ Nat.repr
def String.toSExpr : String → SExpr := atom

instance Nat.HasToSExpr : HasToSExpr Nat := ⟨Nat.toSExpr⟩
instance String.HasToSExpr : HasToSExpr String := ⟨String.toSExpr⟩

protected
def app (f : SExpr) (args : List SExpr) : SExpr := list (f :: args)

end SExpr

export SExpr.HasToSExpr (toSExpr)
