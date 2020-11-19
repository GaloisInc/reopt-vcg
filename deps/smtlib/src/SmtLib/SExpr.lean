import Galois.Data.SExp


abbrev SExpr := WellFormedSExp.SExp String

namespace SExpr

open WellFormedSExp
open WellFormedSExp.SExp

class ToSExpr (a : Type) := (toSExpr : a -> SExpr)

open ToSExpr

instance SExpr.ToSExpr : ToSExpr SExpr := ⟨id⟩

def List.toSExpr {a : Type} [ToSExpr a] (ss : List a) : SExpr :=
list $ ss.map ToSExpr.toSExpr

instance List.ToSExpr {a : Type} [ToSExpr a] : ToSExpr (List a) :=
⟨List.toSExpr⟩

def Nat.toSExpr : Nat → SExpr := atom ∘ Nat.repr
def String.toSExpr : String → SExpr := atom

instance Nat.ToSExpr : ToSExpr Nat := ⟨Nat.toSExpr⟩
instance String.HasToSExpr : ToSExpr String := ⟨String.toSExpr⟩

protected
def app (f : SExpr) (args : List SExpr) : SExpr := list (f :: args)

end SExpr

export SExpr.ToSExpr (toSExpr)
