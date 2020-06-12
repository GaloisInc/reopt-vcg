
import Galois.Data.SExp

namespace Test

namespace SExp

structure Atom :=
(val:String)

def Atom.toString (a:Atom) : String := a.val

instance Atom.HasToString : HasToString Atom := ⟨Atom.toString⟩

def parseAtom (input:String) : Except String Atom := pure $ Atom.mk input

abbrev SExpr := WellFormedSExp.SExp Atom

def parsePass (input : String) : IO String :=
match WellFormedSExp.SExp.readSExp parseAtom input with
| Except.error errMsg => 
  pure $ "unexpected fail on `" ++ input ++ "` with error message `"++errMsg++"`"
| Except.ok sexp => pure $ "pass " ++ sexp.toString

def parseFail (input : String) : IO String :=
match WellFormedSExp.SExp.readSExp parseAtom input with
| Except.error _errMsg => pure $ "fail " ++ input
| Except.ok sexp => pure $ "unexpected pass on `" ++ input ++ "` which parsed as `"++sexp.toString++"`."


def test : IO UInt32 := do
-- Tests that should pass
parsePass "42" >>= IO.println;
parsePass "x" >>= IO.println;
parsePass "()" >>= IO.println;
parsePass "(())" >>= IO.println;
parsePass "(x)" >>= IO.println;
parsePass "( x )" >>= IO.println;
parsePass "(x y)" >>= IO.println;
parsePass "(x(y(z)))" >>= IO.println;
parsePass "(x (y (z)))" >>= IO.println;
-- Tests that should fail
parseFail "(" >>= IO.println;
parseFail "(x" >>= IO.println;
parseFail "(() x" >>= IO.println;
pure 0

end SExp
end Test


