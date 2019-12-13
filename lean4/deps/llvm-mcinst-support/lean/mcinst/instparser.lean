-- Parse instructions as generated via the MCInst interface (essentially att syntax).
-- Instruction is:
--
-- mnemonic\top1,op2,...
--
-- where op1, op2 are:
-- %reg
-- $imm
-- offset OR offset?(base_reg,scale_reg?,scale_imm?)

-- import .common
import init.control.state
import init.control.id
import init.control.option

-- Single-valued, backtracking on failure
structure Parser (tok : Type) (a : Type) :=
  ( run : StateT (List tok) (OptionT Id) a )

namespace Parser

variables {tok a b : Type}

instance : HasOrelse (Parser tok a) := 
  { orelse := fun x y => Parser.mk (x.run <|> y.run) }

instance : Monad (Parser tok) :=
  { bind := fun _ _ x f => Parser.mk (x.run >>= fun v => (f v).run)
  , pure := fun _ x => Parser.mk (pure x)
  }

instance : MonadState (List tok) (Parser tok) :=
  { set := fun s => Parser.mk (set s)
  , get := Parser.mk get
  , modify := fun f => Parser.mk (modify f)
  }

instance : MonadExcept Unit (Parser tok) :=
  { throw := fun _ e => Parser.mk (throw e)
  , catch := fun _ m f => Parser.mk (catch (m.run) (fun x => (f x).run))
  }

partial def many0 (p : Parser tok a) : Unit -> Parser tok (List a)
  | _ => (do v <- p; vs <- many0 (); pure (v :: vs)) <|> pure []

def optional {a : Type} (f : tok -> Option a) : Parser tok a :=
  do tks <- get;
     match tks with     
       | [] => throw ()
       | (t :: tks') => 
         match f t with 
           | none => throw ()
           | some r => (do set tks'; pure r)

def token (f : tok -> Bool) : Parser tok tok :=
  optional (fun t => if f t then some t else none)

def exact [DecidableEq tok] (t : tok) : Parser tok tok :=
  token (fun x => x = t)

def many (p : Parser tok a) : Parser tok (List a) := many0 p ()

def many1 (p : Parser tok a) : Parser tok (List a) := 
  do v <- p; 
     vs <- many p;
     pure (v :: vs)

def sepBy (s : Parser tok b) (p : Parser tok a) : Parser tok (List a) := 
  (do rs <- many (do x <- p; s; pure x); -- p <* s
      -- rs <- pure [];
      r  <- p;
      pure (List.append rs [r])) <|> pure []

def runParser (p : Parser tok a) (tks : List tok) : Option a :=
  (p.run.run' tks).run.run

end Parser

namespace x86

namespace mcinst


def register := String
instance register_has_repr: HasRepr register := ⟨fun s => s⟩

inductive operand 
  | register  : register -> operand
  | immediate : Int -> operand
  | memloc    : Int -> Option register -> Option register -> Nat -> Option register -> operand

def parens (b : String) : String := "(" ++ b ++ ")"

def operand_to_String : operand -> String
  | (operand.register r) => "%" ++ repr r
  -- | (operand.segment s r)    => "(" ++ repr s ++ ":" ++ repr r ++ ")"
  | (operand.immediate v)  => repr v -- ++ "[" ++ repr n ++ "]"
  -- | (operand.rel_immediate off n v) => "(" ++ repr v ++ " + " ++ repr off ++ ")[" ++ repr n ++ "]"
  | (operand.memloc d seg b s i) => 
  (if d = 0 then "" else repr d)
  ++ (match b with 
     | none => "" -- maybe assert everything else is none?
     | some r => 
       parens ("%" ++ repr r ++
       (match i with
        | none => "" 
        | some r' => ",%" ++ repr r' ++ (if s = 1 then "" else "," ++ repr s))))

instance operand_has_repr : HasRepr operand := ⟨operand_to_String⟩

structure instruction :=
  (mnemonic : String)
  (args     : List operand)

instance instruction_has_repr : HasRepr instruction := 
  ⟨fun (i : instruction) => i.mnemonic ++ " " ++ repr i.args⟩

namespace instparser

open Parser

abbreviation OpParser := Parser Char

-- def register := Sigma (fun tp => concrete_reg tp)

def digitP : OpParser Nat :=
  optional (fun c => if c.isDigit then some (c.toNat - '0'.toNat) else none)
  
def natP : OpParser Nat :=
  do ds <- many1 digitP;
     pure (ds.foldl (fun acc d => acc * 10 + d) 0)

def intP : OpParser Int :=
  (do exact '-';
      n <- natP;
      pure (Int.negOfNat n)) <|> 
      (Int.ofNat <$> natP)

def stringP (f : Char -> Bool) : OpParser String := List.asString <$> many (token f)
def string1P (f : Char -> Bool) : OpParser String := List.asString <$> many1 (token f)

def nonWSP : OpParser String := 
  string1P (fun c => not (Char.isWhitespace c))

def registerP : OpParser register :=
  do exact '%';
     string1P Char.isAlphanum

-- offset OR offset?(base_reg,scale_reg?,scale_imm?)
-- we default to 1 for scale_imm if it doesn't exist     
def memlocP : OpParser operand :=
  (do disp <- intP <|> pure 0;
      exact '(';
      base <- registerP;
      (idx, scale) <- (do exact ',';
                          idx <- registerP;
                          scale <- (exact ',' *> natP) <|> pure 1;
                          pure (some idx, scale))
                      <|> pure (none, 1);
      exact ')';
      pure (operand.memloc disp none (some base) scale idx))
  <|>  -- Absolute address
  do disp <- intP; pure (operand.memloc disp none none 0 none)

def operandP : OpParser operand :=
  operand.register <$> registerP
  <|> operand.immediate <$> (exact '$' *> intP)
  <|> memlocP

def instructionP : OpParser instruction :=
  do exact '\t';
     mn <- string1P Char.isAlphanum;
     args <- (exact '\t'*>
              sepBy (do exact ','; exact ' '; pure ()) operandP)
             <|> pure [];
     pure (instruction.mk mn args)
     
end instparser

def parse (s : String) : Option instruction :=
  x86.mcinst.instparser.instructionP.runParser s.toList

end mcinst
end x86

-- def main : List String -> IO UInt32 
--   | [] => pure 1
--   | (x :: xs) => do IO.println (repr (x86.instparser.instructionP.runParser x.toList)); pure 0
