-- A parser combinator library over sexprs

import Init.Control.State
import Init.Control.Id
import Init.Control.Option
import Galois.Data.SExp

open WellFormedSExp

-- Parsing combinators

-- Single-valued, backtracking on failure 
-- Copied from Galois.Data.ParserComb
structure SExpParser (tok : Type) (a : Type) :=
  ( run : StateT (List (SExp tok)) (OptionT Id) a )
  deriving Inhabited

namespace SExpParser

variable {tok a b : Type}

def runSExpParser (p : SExpParser tok a) (sexps : List (SExp tok)) : Option (a × List (SExp tok)) :=
  (p.run.run sexps).run.run

instance : OrElse (SExpParser tok a) := 
  { orElse := fun x y => SExpParser.mk (x.run <|> y.run) }

instance : Monad (SExpParser tok) :=
  { bind := fun x f => SExpParser.mk (x.run >>= fun v => (f v).run)
  , pure := fun x => SExpParser.mk (pure x)
  }

instance : MonadStateOf (List (SExp tok)) (SExpParser tok) :=
  { set := fun s => SExpParser.mk (set s)
  , get := SExpParser.mk get
  , modifyGet := fun f => SExpParser.mk (modifyGet f)
  }

instance : MonadExcept Unit (SExpParser tok) :=
  { throw := fun e => SExpParser.mk (throw e)
  , tryCatch := fun m f => SExpParser.mk (tryCatch (m.run) (fun x => (f x).run))
  }

protected
partial def many0 (p : SExpParser tok a) : Unit -> SExpParser tok (List a)
  | _ => (do let v ← p; let vs ← SExpParser.many0 p (); pure (v :: vs)) <|> pure []

def optional {a : Type} (f : SExp tok -> Option a) : SExpParser tok a :=
  do let tks ← get;
     match tks with     
       | [] => throw ()
       | (t :: tks') => 
         match f t with 
           | none => throw ()
           | some r => (do set tks'; pure r)

def token (f : SExp tok -> Bool) : SExpParser tok (SExp tok) :=
  optional (fun t => if f t then some t else none)

-- def exact [DecidableEq tok] (t : SExp tok) : SExpParser tok Unit :=
--   do _ <- token (fun x => x = t); pure ()

def many (p : SExpParser tok a) : SExpParser tok (List a) := SExpParser.many0 p ()

def many1 (p : SExpParser tok a) : SExpParser tok (List a) := 
  do let v ← p; 
     let vs ← many p;
     pure (v :: vs)

def guard (b : Bool) : SExpParser tok Unit := if b then pure () else throw ()

def first (ps : List (SExpParser tok a)) : SExpParser tok a :=
  List.foldl (fun p m => p <|> m) (throw ()) ps

-- SExp specific parsers
def atom : SExpParser tok tok :=
  optional (fun sexp => match sexp with | SExp.atom a => some a | _ => none)

def list (p : SExpParser tok a) : SExpParser tok a :=
  let go sexp := 
    match sexp with 
    | SExp.atom _  => none
    | SExp.list xs => 
      match runSExpParser p xs with
      | some (v, []) => some v
      | _            => none;
  optional go

def exact [DecidableEq tok] (t : tok) : SExpParser tok Unit :=
  do let a <- atom
     if a = t then pure () else throw ()

end SExpParser

