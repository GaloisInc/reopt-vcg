-- Parsing combinators

import Init.System.IO
import Init.Control.State
import Init.Control.Id
import Init.Control.Option

-- Single-valued, backtracking on failure
structure Parser (tok : Type) (a : Type) :=
  ( run : StateT (List tok) (OptionT Id) a )

namespace Parser

variable {tok a b : Type}

instance : OrElse (Parser tok a) := 
  { orElse := fun x y => Parser.mk (x.run <|> y.run) }

instance : Monad (Parser tok) :=
  { bind := fun x f => Parser.mk (x.run >>= fun v => (f v).run)
  , pure := fun x => Parser.mk (pure x)
  }

instance : MonadStateOf (List tok) (Parser tok) :=
  { set := fun s => Parser.mk (set s)
  , get := Parser.mk get
  , modifyGet := fun f => Parser.mk (modifyGet f)
  }

instance : MonadExcept Unit (Parser tok) :=
  { throw := fun e => Parser.mk (throw e)
  , tryCatch := fun m f => Parser.mk (tryCatch (m.run) (fun x => (f x).run))
  }

protected
partial def many0 (p : Parser tok a) : Unit -> Parser tok (List a)
  | _ => (do let v ← p; let vs ← Parser.many0 p (); pure (v :: vs)) <|> pure []

def optional {a : Type} (f : tok -> Option a) : Parser tok a :=
  do let tks ← get;
     match tks with     
       | [] => throw ()
       | (t :: tks') => 
         match f t with 
           | none => throw ()
           | some r => (do set tks'; pure r)

def token (f : tok -> Bool) : Parser tok tok :=
  optional (fun t => if f t then some t else none)

def exact [DecidableEq tok] (t : tok) : Parser tok Unit :=
  do _ <- token (fun x => x = t); pure ()

def many (p : Parser tok a) : Parser tok (List a) := Parser.many0 p ()

def many1 (p : Parser tok a) : Parser tok (List a) := 
  do let v ← p; 
     let vs ← many p;
     pure (v :: vs)

def sepBy (s : Parser tok b) (p : Parser tok a) : Parser tok (List a) := 
  (do let rs ← many (do let x ← p; discard s; pure x); -- p <* s
      -- rs <- pure [];
      let r  ← p;
      pure (List.append rs [r])) <|> pure []

def first (ps : List (Parser tok a)) : Parser tok a :=
  List.foldl (fun p m => p <|> m) (throw ()) ps

def runParser (p : Parser tok a) (tks : List tok) : Option a :=
  (p.run.run' tks).run.run

end Parser

@[reducible]
def CharParser := Parser Char

namespace CharParser
open Parser

def digitP : CharParser Nat :=
  optional (fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none)

def natP : CharParser Nat :=
  do let ds ← many1 digitP;
     pure (ds.foldl (fun acc d => acc * 10 + d) 0)

def intP : CharParser Int :=
  (do discard $ exact '-';
      let n ← natP;
      pure (Int.negOfNat n)) <|> 
      (Int.ofNat <$> natP)

def stringP (f : Char -> Bool) : CharParser String := List.asString <$> many (token f)
def string1P (f : Char -> Bool) : CharParser String := List.asString <$> many1 (token f)

def nonWSP : CharParser String := 
  string1P (fun c => not (Char.isWhitespace c))

def whitespaceP : CharParser Unit := 
do _ <-token Char.isWhitespace;
   pure ()

def parseFile {a : Type} {m : Type → Type} [Monad m] [MonadLiftT IO m] (p : CharParser a) (fname : String)
  : m (Option a) := 
  do let s ← IO.FS.readFile fname;
     pure (runParser p s.toList)
  

end CharParser
