-- Following the SMTLIB reference v2.6 

import Galois.Init.Nat
import Galois.Data.List
import Galois.Data.SExp
import SmtLib.SExpr

namespace Smt


open WellFormedSExp
open WellFormedSExp.SExp
open SExpr

-- SmtLIB specific sexpr stuff
def indexed (f : SExpr) (args : List SExpr) : SExpr :=
  list $ (atom "_")::f::args

inductive SmtSort : Type
| bool : SmtSort
| bitvec : Nat -> SmtSort
| array  : SmtSort -> SmtSort -> SmtSort

namespace SmtSort

def bv8  := bitvec 8
def bv16 := bitvec 16
def bv32 := bitvec 32
def bv64 := bitvec 64


-- protected def hasDecEq : ∀(a b : SmtSort), Decidable (a = b)
-- | bool, bitvec _ => isFalse (λ h => SmtSort.noConfusion h)
-- | bool, array _ _ => isFalse (λ h => SmtSort.noConfusion h)
-- | bitvec _, bool => isFalse (λ h => SmtSort.noConfusion h)
-- | bitvec _, array _ _ => isFalse (λ h => SmtSort.noConfusion h)
-- | array _ _, bitvec _ => isFalse (λ h => SmtSort.noConfusion h)
-- | array _ _, bool => isFalse (λ h => SmtSort.noConfusion h)
-- | bool, bool => isTrue rfl
-- | bitvec x, bitvec y => 
--   match decEq x y with
--   | isTrue hxy => isTrue (Eq.subst hxy rfl)
--   | isFalse nxy => isFalse (λ h => SmtSort.noConfusion h (λ hxy => absurd hxy nxy))
-- | array a b, array c d =>
--   match hasDecEq a c with
--   | isTrue hac  =>
--     match hasDecEq b d with
--     | isTrue hbd  => isTrue (Eq.subst hac (Eq.subst hbd rfl))
--     | isFalse nbd => isFalse (λ h => SmtSort.noConfusion h (λ _ hnb => absurd hnb nbd))
--   | isFalse nac => isFalse (λ h => SmtSort.noConfusion h (λ hac _ => absurd hac nac))

-- instance : DecidableEq SmtSort := SmtSort.hasDecEq

protected def beq : SmtSort → SmtSort → Bool
| bool, bool => true
| bitvec n, bitvec m => n == m
| array a b, array c d => beq a c && beq b d
| _, _ => false

instance : HasBeq SmtSort := ⟨SmtSort.beq⟩

protected
def toSExpr : SmtSort -> SExpr
| bool => atom "Bool"
| bitvec n => indexed (atom "BitVec") [atom n.repr]
| array k v => list [atom "Array", toSExpr k, toSExpr v]

instance : HasToSExpr SmtSort := ⟨SmtSort.toSExpr⟩

-- *MkDecEq> putStrLn $ mkDecEq "SmtSort" [("bool", []), ("bitvec", [False]), ("array", [True, True])] "decEq"
protected def decEq : ∀(e e' : SmtSort), Decidable (e = e')
| bool, bool => isTrue rfl
| (bitvec c1), (bitvec c1') => 
 (match Nat.decEq c1 c1' with 
  | (isTrue h1) => isTrue (h1 ▸ rfl)
  | (isFalse nh) => isFalse (fun h => SmtSort.noConfusion h $ fun h1' => absurd h1' nh))
| (array c1 c2), (array c1' c2') => 
 (match decEq c1 c1', decEq c2 c2' with 
  | (isTrue h1), (isTrue h2) => isTrue (h1 ▸ h2 ▸ rfl)
  | (isFalse nh), _ => isFalse (fun h => SmtSort.noConfusion h $ fun h1' h2' => absurd h1' nh)
  | (isTrue _), (isFalse nh) => isFalse (fun h => SmtSort.noConfusion h $ fun h1' h2' => absurd h2' nh))
| bool, (bitvec _) => isFalse (fun h => SmtSort.noConfusion h)
| bool, (array _ _) => isFalse (fun h => SmtSort.noConfusion h)
| (bitvec _), bool => isFalse (fun h => SmtSort.noConfusion h)
| (bitvec _), (array _ _) => isFalse (fun h => SmtSort.noConfusion h)
| (array _ _), bool => isFalse (fun h => SmtSort.noConfusion h)
| (array _ _), (bitvec _) => isFalse (fun h => SmtSort.noConfusion h)

instance : DecidableEq SmtSort := SmtSort.decEq

def toString (s:SmtSort) : String := (SmtSort.toSExpr s).toString
instance : HasToString SmtSort := ⟨SmtSort.toString⟩

end SmtSort


-- SmtSorts that work as array keys for `eqrange`
inductive RangeSort
| bitvec : Nat → RangeSort

namespace RangeSort

protected def sort : RangeSort → SmtSort
| bitvec n => SmtSort.bitvec n

end RangeSort


namespace Raw
-- We use lowercase names for types to avoid clashing with Lean

-- This gets around having to have a list of args in term, which currently seems to break lean's 
-- rec function support and codegen

-- Basically a list.
inductive ConstSort : Type 
| base  : SmtSort -> ConstSort
| fsort : SmtSort -> ConstSort -> ConstSort

namespace ConstSort 

def bool := base SmtSort.bool
def bitvec (n : Nat) := base (SmtSort.bitvec n)
def array (k v : SmtSort) := base (SmtSort.array k v)

def funSort (domain : List SmtSort) (codomain : SmtSort) : ConstSort
  := List.foldr (fun x t =>  fsort x t) (base codomain) domain

end ConstSort

def Symbol := String

namespace Symbol

def toSExpr (s : Symbol) : SExpr := atom s

instance : HasToSExpr Symbol := ⟨toSExpr⟩ -- maybe should quote?

end Symbol

-- S3.2
-- inductive SpecConst : Type 
-- | numeral : Nat -> SpecConst
-- | decimal : Nat -> Nat -> SpecConst
-- | binary  : Nat -> Nat -> SpecConst -- nbits and value, subsumes hex (FIXME?)
-- | string  : String -> SpecConst


inductive SpecConst : SmtSort -> Type 
-- | numeral : Nat -> SpecConst
-- | decimal : Nat -> Nat -> SpecConst
| binary (n : Nat): Nat -> SpecConst (SmtSort.bitvec n) -- nbits and value, subsumes hex (FIXME?)
-- | string  : String -> SpecConst



namespace SpecConst 

-- FIXME: copied from bitvec!
section toHex

-- [0 ..< x]
protected def toHexWithLeadingZeros : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  toHexWithLeadingZeros (c::prev) w (Nat.shiftr x 4)

--- Print word as hex
def ppBin (n : Nat) (v : Nat) : String := 
  if n % 4 = 0   
  then "#x" ++ SpecConst.toHexWithLeadingZeros [] (n / 4) v
  else "#b" ++ (List.map (fun i => if Nat.test_bit v i then '1' else '0') (Nat.upto0_lt n)).asString

end toHex

protected
def toSExpr : forall {s : SmtSort}, SpecConst s -> SExpr
-- | numeral n   => Nat.toSExpr n
-- | decimal n f => atom (toString n ++ "." ++ toString f)
| _, binary n v  => atom (ppBin n v)
-- | string s    => String.toSExpr s

instance {s : SmtSort} : HasToSExpr (SpecConst s) := ⟨SpecConst.toSExpr⟩

end SpecConst


namespace BuiltinIdent

open SmtSort
open Nat

abbrev unop (a : SmtSort) (b : SmtSort) : ConstSort :=
  ConstSort.fsort a (ConstSort.base b)

abbrev binop (a : SmtSort) (b : SmtSort) (c : SmtSort) : ConstSort :=
  ConstSort.fsort a (ConstSort.fsort b (ConstSort.base c))

abbrev ternop (a : SmtSort) (b : SmtSort) (c : SmtSort) (d : SmtSort) : ConstSort :=
  ConstSort.fsort a (binop b c d)

abbrev quadop (a : SmtSort) (b : SmtSort) (c : SmtSort) (d : SmtSort) (e : SmtSort) : ConstSort :=
  ConstSort.fsort a (ternop b c d e)

end BuiltinIdent

section

open SmtSort
open Nat
open BuiltinIdent

@[reducible]
def nary (s : SmtSort) (t : SmtSort) : Nat -> ConstSort 
| zero   => ConstSort.base t
| succ n => ConstSort.fsort s (nary n) 

-- distinct is a term as it has arbitrary arity
inductive BuiltinIdent : ConstSort -> Type
-- * Core theory
| true                : BuiltinIdent ConstSort.bool
| false               : BuiltinIdent ConstSort.bool
| not                 : BuiltinIdent (unop bool bool)
| impl                : BuiltinIdent (binop bool bool bool)
| and                 : BuiltinIdent (binop bool bool bool)
| or                  : BuiltinIdent (binop bool bool bool)
| xor                 : BuiltinIdent (binop bool bool bool)
| eq       (s : SmtSort) : BuiltinIdent (binop s s bool)
| smtIte   (s : SmtSort) : BuiltinIdent (ConstSort.fsort bool (binop s s s))
| distinct (s : SmtSort) (arity : Nat)
                      : BuiltinIdent (nary s bool arity)

-- * Arrays
| select (k v : SmtSort) : BuiltinIdent (binop (array k v) k v)
| store  (k v : SmtSort) : BuiltinIdent (ternop (array k v) k v (array k v))

-- CVC4 specific
| eqrange (k : RangeSort) (v : SmtSort) : BuiltinIdent (quadop (array k.sort v) (array k.sort v) k.sort k.sort bool)

-- * BitVecs
-- hex/binary literals
| concat  (n : Nat) (m : Nat) : BuiltinIdent (binop (bitvec n) (bitvec m) (bitvec (n + m)))
| extract (n : Nat) (i : Nat) (j : Nat)                   
                              : BuiltinIdent (unop (bitvec n) (bitvec (i + 1 - j)))
-- -- unops
| bvnot   (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec n))
| bvneg   (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec n))
-- -- binops
| bvand   (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvor    (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvadd   (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvmul   (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvudiv  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvurem  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvshl   (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvlshr  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
-- comparison
| bvult   (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)

-- Functions defined by Smt as abbrevs.
| bvnand (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvnor  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvxor  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvxnor (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvcomp (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec 1))
| bvsub  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvsdiv (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvsrem (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvsmod (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))
| bvashr (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) (bitvec n))

-- Defined, param by i >= 1
| repeat (i : Nat) (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec (i * n)))

-- Defined, param by i >= 0
| zeroExtend  (i : Nat) (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec (n + i)))
| signExtend  (i : Nat) (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec (n + i)))
| rotateLeft  (i : Nat) (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec n))
| rotateRight (i : Nat) (n : Nat) : BuiltinIdent (unop (bitvec n) (bitvec n))

| bvule                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvugt                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvuge                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvslt                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvsle                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvsgt                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)
| bvsge                  (n : Nat) : BuiltinIdent (binop (bitvec n) (bitvec n) bool)

end 

namespace BuiltinIdent

protected 
def toSExpr : forall {cs : ConstSort}, BuiltinIdent cs -> SExpr
-- * Core theory
| _, true                 => atom "true"
| _, false                => atom "false"
| _, not                  => atom "not"
| _, impl                 => atom "=>"
| _, and                  => atom "and"
| _, or                   => atom "or"
| _, xor                  => atom "xor"
| _, eq _                 => atom "="
| _, smtIte _             => atom "ite"
| _, distinct _ _         => atom "distinct"

| _, select _ _           => atom "select"
| _, store  _ _           => atom "store"
| _, eqrange _ _          => atom "eqrange"

-- * BitVecs
-- hex/binary literals
| _, concat _ _           => atom "concat"
| _, extract _ i j        => indexed (atom "extract") [Nat.toSExpr i, Nat.toSExpr j]
-- unops
| _, bvnot   _            => atom "bvnot"
| _, bvneg   _            => atom "bvneg"
-- binops                   
| _, bvand   _            => atom "bvand"
| _, bvor    _            => atom "bvor"
| _, bvadd   _            => atom "bvadd"
| _, bvmul   _            => atom "bvmul"
| _, bvudiv  _            => atom "bvudiv"
| _, bvurem  _            => atom "bvurem"
| _, bvshl   _            => atom "bvshl"
| _, bvlshr  _            => atom "bvlshr"
-- comparison               
| _, bvult   _            => atom "bvult"

| _, bvnand  _            => atom "bvnand" 
| _, bvnor   _            => atom "bvnor" 
| _, bvxor   _            => atom "bvxor"  
| _, bvxnor  _            => atom "bvxnor"  
| _, bvcomp  _            => atom "bvcomp" 
| _, bvsub   _            => atom "bvsub" 
| _, bvsdiv  _            => atom "bvsdiv"
| _, bvsrem  _            => atom "bvsrem" 
| _, bvsmod  _            => atom "bvsmod" 
| _, bvashr  _            => atom "bvashr" 

| _, repeat i _           => indexed (atom "repeat") [Nat.toSExpr i]

| _, zeroExtend  i _     => indexed (atom "zero_extend")  [Nat.toSExpr i]
| _, signExtend  i _     => indexed (atom "sign_extend")  [Nat.toSExpr i]
| _, rotateLeft  i _     => indexed (atom "rotate_left")  [Nat.toSExpr i]
| _, rotateRight i _     => indexed (atom "rotate_right") [Nat.toSExpr i]

| _, bvule _              => atom "bvule" 
| _, bvugt _              => atom "bvugt" 
| _, bvuge _              => atom "bvuge" 
| _, bvslt _              => atom "bvslt" 
| _, bvsle _              => atom "bvsle" 
| _, bvsgt _              => atom "bvsgt" 
| _, bvsge _              => atom "bvsge" 

instance {cs : ConstSort} : HasToSExpr (BuiltinIdent cs) := ⟨BuiltinIdent.toSExpr⟩

end BuiltinIdent

inductive Ident : ConstSort -> Type 
| symbol (cs : ConstSort)  : Symbol -> Ident cs
| builtin {cs : ConstSort} : BuiltinIdent cs -> Ident cs

namespace Ident

protected
def toSExpr : forall {cs : ConstSort}, Ident cs -> SExpr
| _, symbol _ s => atom s
| _, builtin bi => BuiltinIdent.toSExpr bi

instance {cs : ConstSort} : HasToSExpr (Ident cs)  := ⟨Ident.toSExpr⟩

end Ident

structure SortedVar (sort : SmtSort) : Type  :=
(var : Symbol)

namespace SortedVar 

protected
def toSExpr : forall {s : SmtSort}, SortedVar s -> SExpr
| s, x => List.toSExpr [Symbol.toSExpr x.var, SmtSort.toSExpr s]

instance {s : SmtSort} : HasToSExpr (SortedVar s)  := ⟨SortedVar.toSExpr⟩

end SortedVar

-- S3.6
-- Use typed terms?
inductive Term : ConstSort -> Type
| const (s : SmtSort) : SpecConst s -> Term (ConstSort.base s)
| ident {cs : ConstSort} : Ident cs -> Term cs
| app {s : SmtSort} {cs : ConstSort} : Term (ConstSort.fsort s cs)
                                    -> Term (ConstSort.base s) -> Term cs
| smtLet {s t : SmtSort} : Symbol -> Term (ConstSort.base t)
                       -> Term (ConstSort.base s)
                       -> Term (ConstSort.base s) -- single binding only
| smtForall {s : SmtSort} : SortedVar s -> Term ConstSort.bool -> Term ConstSort.bool
| smtExists {s : SmtSort} : SortedVar s -> Term ConstSort.bool -> Term ConstSort.bool

namespace Term

-- Include a proof that relates the length of the sexpr list to the arity of the cs?x
protected
def toSExprAux : forall {cs : ConstSort} (t : Term cs), List SExpr -> SExpr
| _, const _ sc, _           => toSExpr sc
-- identifier with base type, like 'true'
| _, ident x, []    => toSExpr x
| _, ident x, args  => SExpr.app (toSExpr x) args
| _, app f x, args           => toSExprAux f (toSExprAux x [] :: args)
| _, smtLet v e body, _     => toSExpr [atom "let"
                                        , toSExpr [toSExpr [toSExpr v, toSExprAux e []]]
                                        , toSExprAux body []]
| _, smtForall v body, _    => SExpr.app (atom "forall") [toSExpr [toSExpr v], toSExprAux body []]
| _, smtExists v body, _    => SExpr.app (atom "exists") [toSExpr [toSExpr v], toSExprAux body []]

def toSExpr {cs : ConstSort} (tm : Term cs) : SExpr := Term.toSExprAux tm []

instance {cs : ConstSort} : HasToSExpr (Term cs) := ⟨Term.toSExpr⟩

end Term

inductive Logic
| all

namespace Logic

def toString : Logic → String
| all => "ALL"

end Logic

inductive Opt
| produceModels : Bool → Opt

namespace Opt

def toSExprs : Opt → List SExpr
| produceModels b => [atom ":produce-models", (if b then (atom "true") else (atom "false"))]

end Opt


-- Scripts and Commands (S3.9)

inductive Command
| assert : Term ConstSort.bool -> Command
| setLogic : Logic → Command
| setOption : Opt → Command
| checkSatAssuming : List (Term ConstSort.bool) → Command
| comment : String → Command
| exit : Command
-- | check_sat : Command

-- Not supported yet
-- | ( declare-datatype ⟨symbol⟩ ⟨datatype_dec⟩)
-- | ( declare-datatypes ( ⟨sort_dec ⟩n+1 ) ( ⟨datatype_dec ⟩n+1 ) ) | ( declare-fun ⟨symbol ⟩ ( ⟨sort ⟩∗ ) ⟨sort ⟩ )
-- | ( declare-sort ⟨symbol ⟩ ⟨numeral ⟩ ) -- not yet supported
-- | ( define-fun-rec ⟨function_def ⟩ )
-- | ( define-funs-rec ( ⟨function_dec⟩n+1 ) ( ⟨term⟩n+1 ) )
-- | ( define-sort ⟨symbol ⟩ ( ⟨symbol ⟩∗ ) ⟨sort ⟩ )

-- Syntactic sugar for declare-fun
-- | declare-const ⟨symbol ⟩ ⟨sort ⟩ )
| declareFun : Symbol -> List SmtSort -> SmtSort -> Command
| defineFun  : Symbol -> List (Sigma SortedVar)
                -> forall (s : SmtSort), Term (ConstSort.base s) -> Command

-- | echo : String -> Command
-- | ( get-assertions )
-- | ( get-assignment )
-- | ( get-info ⟨info_flag ⟩ )
-- | ( get-model )
-- | ( get-option ⟨keyword ⟩ )
-- | ( get-proof )
-- | ( get-unsat-assumptions )
-- | ( get-unsat-core )
-- | ( get-value ( ⟨term⟩+ ) )
-- | ( pop ⟨numeral ⟩ )
-- | ( push ⟨numeral ⟩ )
-- | ( reset )
-- | ( reset-assertions )
-- | ( set-info ⟨attribute ⟩ )
-- | ( set-logic ⟨symbol ⟩ )
-- | ( set-option ⟨option⟩ )

namespace Command

def toSExprSigma : Sigma SortedVar -> SExpr
| Sigma.mk _ tm => toSExpr tm

protected 
def toSExpr : Command -> SExpr 
| assert tm              => SExpr.app (atom "assert") [Term.toSExpr tm]
| declareFun s args r   => SExpr.app (atom "declare-fun") [Symbol.toSExpr s, List.toSExpr args, SmtSort.toSExpr r]
| defineFun  s args r b => SExpr.app (atom "define-fun") [Symbol.toSExpr s, List.toSExpr (args.map toSExprSigma), SmtSort.toSExpr r
                                                          , Term.toSExpr b]
| setLogic l =>
  SExpr.app (atom "set-logic") [atom l.toString]
| setOption opt =>
  SExpr.app (atom "set-option") opt.toSExprs
| checkSatAssuming assumptions =>
  list [(atom "check-sat-assuming"), list $ assumptions.map Term.toSExpr]
| comment content =>
  let body : List Char := content.data.joinMap (λ c => if c == '\n' then ['\n',';',' '] else [c]);
  atom $ "; " ++ body.asString ++ "\n"
| exit => SExpr.app (atom "exit") []

instance : HasToSExpr Command := ⟨Command.toSExpr⟩

def isComment : Command → Bool
| comment _ => true
| _ => false

end Command

end Raw



end Smt
