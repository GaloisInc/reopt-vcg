-- Following the SMTLIB reference v2.6 

import Galois.Init.Nat

namespace SExpr

structure SExpr := (sexpr : String)

instance SExpr.HasToString : HasToString SExpr := ⟨fun (s : SExpr) => s.sexpr⟩

def atom : String -> SExpr := SExpr.mk

class HasToSExpr (a : Type) := (toSExpr : a -> SExpr)

open HasToSExpr

instance SExpr.HasToSExpr : HasToSExpr SExpr := ⟨id⟩

instance List.HasToSExpr {a : Type} [HasToSExpr a] : HasToSExpr (List a) :=
  ⟨fun ss => SExpr.mk ("(" ++ ss.foldr (fun a s => (HasToSExpr.toSExpr a).sexpr ++ " " ++ s) ")")⟩

instance Nat.HasToSExpr : HasToSExpr Nat := ⟨fun n => SExpr.mk (toString n)⟩

instance String.HasToSExpr : HasToSExpr String := ⟨fun s => SExpr.mk ("\"" ++ s ++ "\"")⟩

protected
def app (f : SExpr) (args : List SExpr) : SExpr := toSExpr (f :: args)

end SExpr


export SExpr.HasToSExpr (toSExpr)


namespace SMT

open SExpr
open SExpr.HasToSExpr

-- SMTLIB specific sexpr stuff
def indexed (f : SExpr) (args : List SExpr) : SExpr :=
  SExpr.app (atom "_") (f :: args)

inductive sort : Type
| smt_bool : sort
| bitvec : Nat -> sort
| array  : sort -> sort -> sort

namespace sort

def bv8  := bitvec 8
def bv16 := bitvec 16
def bv32 := bitvec 32
def bv64 := bitvec 64


-- protected def hasDecEq : ∀(a b : sort), Decidable (a = b)
-- | smt_bool, bitvec _ => isFalse (λ h => sort.noConfusion h)
-- | smt_bool, array _ _ => isFalse (λ h => sort.noConfusion h)
-- | bitvec _, smt_bool => isFalse (λ h => sort.noConfusion h)
-- | bitvec _, array _ _ => isFalse (λ h => sort.noConfusion h)
-- | array _ _, bitvec _ => isFalse (λ h => sort.noConfusion h)
-- | array _ _, smt_bool => isFalse (λ h => sort.noConfusion h)
-- | smt_bool, smt_bool => isTrue rfl
-- | bitvec x, bitvec y => 
--   match decEq x y with
--   | isTrue hxy => isTrue (Eq.subst hxy rfl)
--   | isFalse nxy => isFalse (λ h => sort.noConfusion h (λ hxy => absurd hxy nxy))
-- | array a b, array c d =>
--   match hasDecEq a c with
--   | isTrue hac  =>
--     match hasDecEq b d with
--     | isTrue hbd  => isTrue (Eq.subst hac (Eq.subst hbd rfl))
--     | isFalse nbd => isFalse (λ h => sort.noConfusion h (λ _ hnb => absurd hnb nbd))
--   | isFalse nac => isFalse (λ h => sort.noConfusion h (λ hac _ => absurd hac nac))

-- instance : DecidableEq sort := sort.hasDecEq

protected def beq : sort → sort → Bool
| smt_bool, smt_bool => true
| bitvec n, bitvec m => n == m
| array a b, array c d => beq a c && beq b d
| _, _ => false

instance : HasBeq sort := ⟨sort.beq⟩

protected
def to_sexpr : sort -> SExpr
| smt_bool => atom "Bool"
| bitvec n => indexed (atom "BitVec") [toSExpr n]
| array k v => SExpr.app (atom "Array") [to_sexpr k, to_sexpr v]

instance : HasToSExpr sort := ⟨sort.to_sexpr⟩

-- *MkDecEq> putStrLn $ mkDecEq "sort" [("smt_bool", []), ("bitvec", [False]), ("array", [True, True])] "decidable_eq"
protected def decidable_eq : ∀(e e' : sort), Decidable (e = e')
| smt_bool, smt_bool => isTrue rfl
| (bitvec c1), (bitvec c1') => 
 (match decEq c1 c1' with 
  | (isTrue h1) => isTrue (h1 ▸ rfl)
  | (isFalse nh) => isFalse (fun h => sort.noConfusion h $ fun h1' => absurd h1' nh))
| (array c1 c2), (array c1' c2') => 
 (match decidable_eq c1 c1', decidable_eq c2 c2' with 
  | (isTrue h1), (isTrue h2) => isTrue (h1 ▸ h2 ▸ rfl)
  | (isFalse nh), _ => isFalse (fun h => sort.noConfusion h $ fun h1' h2' => absurd h1' nh)
  | (isTrue _), (isFalse nh) => isFalse (fun h => sort.noConfusion h $ fun h1' h2' => absurd h2' nh))
| smt_bool, (bitvec _) => isFalse (fun h => sort.noConfusion h)
| smt_bool, (array _ _) => isFalse (fun h => sort.noConfusion h)
| (bitvec _), smt_bool => isFalse (fun h => sort.noConfusion h)
| (bitvec _), (array _ _) => isFalse (fun h => sort.noConfusion h)
| (array _ _), smt_bool => isFalse (fun h => sort.noConfusion h)
| (array _ _), (bitvec _) => isFalse (fun h => sort.noConfusion h)

instance : DecidableEq sort := sort.decidable_eq
          
def toString (s:sort) := s.to_sexpr.sexpr

instance : HasToString sort := ⟨sort.toString⟩

end sort

namespace Raw
-- We use lowercase names for types to avoid clashing with Lean

-- This gets around having to have a list of args in term, which currently seems to break lean's 
-- rec function support and codegen

-- Basically a list.
inductive const_sort : Type 
| base  : sort -> const_sort
| fsort : sort -> const_sort -> const_sort

namespace const_sort 

def smt_bool := base sort.smt_bool
def bitvec (n : Nat) := base (sort.bitvec n)
def array (k v : sort) := base (sort.array k v)

end const_sort

def symbol := String

namespace symbol

instance : HasToSExpr symbol := ⟨atom⟩ -- maybe should quote?

end symbol

-- S3.2
inductive spec_constant : Type 
| numeral : Nat -> spec_constant
| decimal : Nat -> Nat -> spec_constant
| binary  : Nat -> Nat -> spec_constant -- nbits and value, subsumes hex (FIXME?)
| string  : String -> spec_constant

namespace spec_constant 

-- FIXME: copied from bitvec!
section to_hex

-- [0 ..< x]
protected def to_hex_with_leading_zeros : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex_with_leading_zeros (c::prev) w (Nat.shiftr x 4)

--- Print word as hex
def pp_bin (n : Nat) (v : Nat) : String := 
  if n % 4 = 0   
  then "#x" ++ spec_constant.to_hex_with_leading_zeros [] (n / 4) v
  else "#b" ++ (List.map (fun i => if Nat.test_bit v i then '1' else '0') (Nat.upto0_lt n)).asString

end to_hex

protected
def to_sexpr : spec_constant -> SExpr
| numeral n   => toSExpr n
| decimal n f => atom (toString n ++ "." ++ toString f)
| binary n v  => atom (pp_bin n v)
| string s    => toSExpr s

instance : HasToSExpr spec_constant := ⟨spec_constant.to_sexpr⟩

end spec_constant

namespace builtin_identifier

open sort
open Nat

abbrev unop (a : sort) (b : sort) : const_sort :=
  const_sort.fsort a (const_sort.base b)

abbrev binop (a : sort) (b : sort) (c : sort) : const_sort :=
  const_sort.fsort a (const_sort.fsort b (const_sort.base c))

abbrev ternop (a : sort) (b : sort) (c : sort) (d : sort) : const_sort :=
  const_sort.fsort a (const_sort.fsort b (const_sort.fsort c (const_sort.base d)))

end builtin_identifier

section

open sort
open Nat
open builtin_identifier

def nary (s : sort) (t : sort) : Nat -> const_sort 
| zero   => const_sort.base t
| succ n => const_sort.fsort s (nary n) 

-- distinct is a term as it has arbitrary arity
inductive builtin_identifier : const_sort -> Type
-- * Core theory
| true                : builtin_identifier const_sort.smt_bool
| false               : builtin_identifier const_sort.smt_bool
| not                 : builtin_identifier (unop smt_bool smt_bool)
| impl                : builtin_identifier (binop smt_bool smt_bool smt_bool)
| and                 : builtin_identifier (binop smt_bool smt_bool smt_bool)
| or                  : builtin_identifier (binop smt_bool smt_bool smt_bool)
| xor                 : builtin_identifier (binop smt_bool smt_bool smt_bool)
| eq       (s : sort) : builtin_identifier (binop s s smt_bool)
| smt_ite  (s : sort) : builtin_identifier (const_sort.fsort smt_bool (binop s s s))
| distinct (s : sort) (arity : Nat)
                      : builtin_identifier (nary s smt_bool arity)

-- * Arrays
| select (k v : sort) : builtin_identifier (binop (array k v) k v)
| store  (k v : sort) : builtin_identifier (ternop (array k v) k v (array k v))

-- * BitVecs
-- hex/binary literals
| concat  (n : Nat) (m : Nat) : builtin_identifier (binop (bitvec n) (bitvec m) (bitvec (n + m)))
| extract (n : Nat) (i : Nat) (j : Nat)                   
                              : builtin_identifier (unop (bitvec n) (bitvec (i + 1 - j)))
-- -- unops
| bvnot   (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec n))
| bvneg   (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec n))
-- -- binops
| bvand   (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvor    (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvadd   (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvmul   (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvudiv  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvurem  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvshl   (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvlshr  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
-- comparison
| bvult   (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)

-- Functions defined by SMT as abbrevs.
| bvnand (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvnor  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvxor  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvxnor (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvcomp (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec 1))
| bvsub  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvsdiv (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvsrem (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvsmod (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))
| bvashr (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) (bitvec n))

-- Defined, param by i >= 1
| repeat (i : Nat) (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec (i * n)))

-- Defined, param by i >= 0
| zero_extend  (i : Nat) (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec (n + i)))
| sign_extend  (i : Nat) (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec (n + i)))
| rotate_left  (i : Nat) (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec n))
| rotate_right (i : Nat) (n : Nat) : builtin_identifier (unop (bitvec n) (bitvec n))

| bvule                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvugt                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvuge                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvslt                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvsle                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvsgt                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)
| bvsge                  (n : Nat) : builtin_identifier (binop (bitvec n) (bitvec n) smt_bool)

end 

namespace builtin_identifier

protected 
def to_sexpr : forall {cs : const_sort}, builtin_identifier cs -> SExpr
-- * Core theory
| _, true                 => atom "true"
| _, false                => atom "false"
| _, not                  => atom "not"
| _, impl                 => atom "impl"
| _, and                  => atom "and"
| _, or                   => atom "or"
| _, xor                  => atom "xor"
| _, eq       _           => atom "eq"
| _, smt_ite  _           => atom "smt_ite"
| _, distinct _ _         => atom "distinct"

| _, select _ _           => atom "select"
| _, store  _ _           => atom "store"

-- * BitVecs
-- hex/binary literals
| _, concat _ _           => atom "concat"
| _, extract _ i j        => indexed (atom "extract") [toSExpr i, toSExpr j]
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

| _, repeat i _           => indexed (atom "repeat") [toSExpr i]

| _, zero_extend  i _     => indexed (atom "zero_extend")  [toSExpr i]
| _, sign_extend  i _     => indexed (atom "sign_extend")  [toSExpr i]
| _, rotate_left  i _     => indexed (atom "rotate_left")  [toSExpr i]
| _, rotate_right i _     => indexed (atom "rotate_right") [toSExpr i]

| _, bvule _              => atom "bvule" 
| _, bvugt _              => atom "bvugt" 
| _, bvuge _              => atom "bvuge" 
| _, bvslt _              => atom "bvslt" 
| _, bvsle _              => atom "bvsle" 
| _, bvsgt _              => atom "bvsgt" 
| _, bvsge _              => atom "bvsge" 

instance {cs : const_sort} : HasToSExpr (builtin_identifier cs) := ⟨builtin_identifier.to_sexpr⟩

end builtin_identifier

inductive identifier : const_sort -> Type 
| symbol (cs : const_sort)  : symbol -> identifier cs
| builtin {cs : const_sort} : builtin_identifier cs -> identifier cs

namespace identifier

protected
def to_sexpr : forall {cs : const_sort}, identifier cs -> SExpr
| _, symbol _ s => atom s
| _, builtin bi => toSExpr bi

instance {cs : const_sort} : HasToSExpr (identifier cs)  := ⟨identifier.to_sexpr⟩

end identifier

inductive sorted_var : sort -> Type 
| mk (s : sort) : symbol -> sorted_var s
  
namespace sorted_var 

protected
def to_sexpr : forall {s : sort}, sorted_var s -> SExpr
| _, mk s v => toSExpr [toSExpr v, toSExpr s]

instance {s : sort} : HasToSExpr (sorted_var s)  := ⟨sorted_var.to_sexpr⟩

end sorted_var

-- S3.6
-- Use typed terms?
inductive term : const_sort -> Type
| const (s : sort) : spec_constant -> term (const_sort.base s)
| identifier {cs : const_sort} : identifier cs -> term cs
| app {s : sort} {cs : const_sort} : term (const_sort.fsort s cs)
                                    -> term (const_sort.base s) -> term cs
| smt_let {s t : sort} : symbol -> term (const_sort.base t)
                       -> term (const_sort.base s)
                       -> term (const_sort.base s) -- single binding only
| smt_forall {s : sort} : sorted_var s -> term const_sort.smt_bool -> term const_sort.smt_bool
| smt_exists {s : sort} : sorted_var s -> term const_sort.smt_bool -> term const_sort.smt_bool

namespace term

-- Include a proof that relates the length of the sexpr list to the arity of the cs?x
protected
def to_sexpr_aux : forall {cs : const_sort} (t : term cs), List SExpr -> SExpr
| _, const _ sc, _           => toSExpr sc
-- identifier with base type, like 'true'
| _, identifier ident, []    => toSExpr ident
| _, identifier ident, args  => SExpr.app (toSExpr ident) args
| _, app f x, args           => to_sexpr_aux f (to_sexpr_aux x [] :: args)
| _, smt_let v e body, _     => toSExpr [atom "let"
                                        , toSExpr [toSExpr v, to_sexpr_aux e []]
                                        , to_sexpr_aux body []]
| _, smt_forall v body, _    => SExpr.app (atom "forall") [toSExpr [toSExpr v], to_sexpr_aux body []]
| _, smt_exists v body, _    => SExpr.app (atom "exists") [toSExpr [toSExpr v], to_sexpr_aux body []]

instance {cs : const_sort} : HasToSExpr (term cs) := ⟨fun tm => term.to_sexpr_aux tm []⟩

end term



-- Scripts and Commands (S3.9)

inductive command : Type 
| assert : term const_sort.smt_bool -> command

-- | check_sat : command

-- Not supported yet
-- | ( check-sat-assuming ( ⟨prop_literal ⟩∗ ) )
-- | ( declare-datatype ⟨symbol⟩ ⟨datatype_dec⟩)
-- | ( declare-datatypes ( ⟨sort_dec ⟩n+1 ) ( ⟨datatype_dec ⟩n+1 ) ) | ( declare-fun ⟨symbol ⟩ ( ⟨sort ⟩∗ ) ⟨sort ⟩ )
-- | ( declare-sort ⟨symbol ⟩ ⟨numeral ⟩ ) -- not yet supported
-- | ( define-fun-rec ⟨function_def ⟩ )
-- | ( define-funs-rec ( ⟨function_dec⟩n+1 ) ( ⟨term⟩n+1 ) )
-- | ( define-sort ⟨symbol ⟩ ( ⟨symbol ⟩∗ ) ⟨sort ⟩ )

-- Syntactic sugar for declare-fun
-- | declare-const ⟨symbol ⟩ ⟨sort ⟩ )
| declare_fun : symbol -> List sort -> sort -> command
| define_fun  : symbol -> List (Sigma sorted_var)
                -> forall (s : sort), term (const_sort.base s) -> command

-- | echo : String -> command
-- | exit : command
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

namespace command

def to_sexpr_sigma : Sigma sorted_var -> SExpr
| Sigma.mk _ tm => toSExpr tm

protected 
def to_sexpr : command -> SExpr 
| assert tm              => SExpr.app (atom "assert") [toSExpr tm]
| declare_fun s args r   => SExpr.app (atom "declare-fun") [toSExpr s, toSExpr (args.map toSExpr), toSExpr r]
| define_fun  s args r b => SExpr.app (atom "define-fun") [toSExpr s, toSExpr (args.map to_sexpr_sigma), toSExpr r
                                                          , toSExpr b]
instance : HasToSExpr command := ⟨command.to_sexpr⟩

end command

end Raw

-- *** Exported API ***
open sort


def term (s : sort) := Raw.term (Raw.const_sort.base s)
instance term.HasToSExpr (s : sort) : HasToSExpr (term s) := 
  inferInstanceAs (HasToSExpr (Raw.term (Raw.const_sort.base s)))

def symbol := Raw.symbol

@[reducible]
def  command := Raw.command

-- def identifier := Raw.identifier

@[reducible]
def args_to_type (ss : List sort) (res : sort) : Type 
  := List.foldr (fun x t => term x -> t) (term res) ss
-- | [], res        => term res
-- | (x :: xs), res => term x -> args_to_type xs res

-- -- given ident [a, b, c] and d, turns teram a -> term b -> term c -> term d into (ident [a, b, c])
-- def app_ident_aux (cs : const_sort) (ident : identifier cs) 
--   : sorted_list term cs.args -> args_to_type cs.args cs.result
-- | nil             => Raw.term.app_ident ident args.reverse
-- | (s :: ss), args => fun (t_s : term s) => app_ident_aux ss (t_s :: args)

-- def app_ident  {args : List sort} {res : sort} (ident : identifier args res) : args_to_type args res
--   := app_ident_aux res ident args []

section
open Raw.term
open Raw.builtin_identifier
open Raw.identifier
open Raw.command
open Raw (const_sort)
open Raw.const_sort (fsort base)
open Raw (spec_constant)
open Raw.spec_constant

def const_sort_to_type : const_sort -> Type 
| base s    => term s
| fsort s t => term s -> const_sort_to_type t


def mk_symbol (sym : symbol) (s : sort) : term s := 
  Raw.term.identifier (Raw.identifier.symbol (Raw.const_sort.base s) sym)  


namespace Raw.identifier

-- inductive sorted_list (f : sort -> Type) : List sort -> Type 
-- | nil  : sorted_list []
-- | cons {s : sort} {ss : List sort} : f s -> sorted_list ss -> sorted_list (s :: ss)

protected
def expand_ident_aux : forall {cs : const_sort}, Raw.term cs -> const_sort_to_type cs
| base s, i    => i
| fsort s t, i => fun x => expand_ident_aux (app i x)

def expand_ident {cs : const_sort} (i : Raw.identifier cs) : const_sort_to_type cs :=
  Raw.identifier.expand_ident_aux (identifier i)

end Raw.identifier

private
def unop {s t : sort} (i : Raw.builtin_identifier (Raw.builtin_identifier.unop s t)) (a : term s)
  : term t := app (identifier (builtin i)) a

private
def binop {a b c : sort} (i : Raw.builtin_identifier (Raw.builtin_identifier.binop a b c)) 
          (x : term a) (y : term b) : term c := app (app (identifier (builtin i)) x) y

private
def ternop {a b c d : sort} 
           (i : Raw.builtin_identifier (Raw.const_sort.fsort a (Raw.builtin_identifier.binop b c d))) 
           (x : term a) (y : term b) (z : term c) : term d 
           := app (app (app (identifier (builtin i)) x) y) z

-- Builtin terms
def true  : term smt_bool                           := identifier (builtin true)
def false : term smt_bool                           := identifier (builtin false)
def not   : term smt_bool -> term smt_bool          := unop not
def impl  : term smt_bool -> term smt_bool -> term smt_bool := binop impl
def and   : term smt_bool -> term smt_bool -> term smt_bool := binop and
def or    : term smt_bool -> term smt_bool -> term smt_bool := binop or
def xor   : term smt_bool -> term smt_bool -> term smt_bool := binop xor
def eq {a : sort} : term a -> term a -> term smt_bool       := binop (eq a)
-- FIXME
-- def distinct {a : sort} : List (term a) -> term smt_bool := Raw.term.distinct
def smt_ite  {a : sort} : term smt_bool -> term a -> term a -> term a := ternop (smt_ite a)

-- Arrays
def select (k v : sort) : term (array k v) -> term k -> term v :=
  binop (select k v)

def store  (k v : sort) : term (array k v) -> term k -> term v -> term (array k v) :=
  ternop (store k v)

-- BitVecs
-- hex/binary literals
def bvimm (n v : Nat) : term (bitvec n) := const (bitvec n) (binary n v)
-- c.f. bitvec.of_int 
def bvimm' (n : Nat) : Int -> term (bitvec n)
| Int.ofNat x   => bvimm n x
| Int.negSucc x => bvimm n (Nat.ldiff (2^n-1) x)

def concat {n m : Nat} : term (bitvec n) -> term (bitvec m) -> term (bitvec (n + m)) := 
  binop (concat n m)
def extract {n : Nat} (i : Nat) (j : Nat) : term (bitvec n) -> term (bitvec (i + 1 - j)) :=
  unop (extract n i j)
def bvnot {n : Nat} : term (bitvec n) -> term (bitvec n) := unop (bvnot n)
def bvneg {n : Nat} : term (bitvec n) -> term (bitvec n) := unop (bvneg n)

-- binops
def bvand {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvand  n)
def bvor  {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvor   n)
def bvadd {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvadd  n)
def bvmul {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvmul  n)
def bvudiv {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := binop (bvudiv n)
def bvurem {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := binop (bvurem n)
def bvshl {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvshl  n)
def bvlshr {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := binop (bvlshr n)
-- comparison
def bvult {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvult n)


-- Functions defined by SMT as abbrevs.
def bvnand {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvnand n) 
def bvnor  {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvnor  n) 
def bvxor  {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvxor  n) 
def bvxnor {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvxnor n) 
def bvcomp {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec 1)  := binop (bvcomp n)
def bvsub  {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvsub  n) 
def bvsdiv {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvsdiv n) 
def bvsrem {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvsrem n) 
def bvsmod {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvsmod n) 
def bvashr {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n)  := binop (bvashr n) 

-- Defined, param by i >= 1
def repeat {n : Nat} (i : Nat) : term (bitvec n) -> term (bitvec (i * n)) := unop (repeat i n)

-- Defined, param by i >= 0
def zero_extend  {n : Nat} (i : Nat) : term (bitvec n) -> term (bitvec (n + i)) := unop (zero_extend  i n) 
def sign_extend  {n : Nat} (i : Nat) : term (bitvec n) -> term (bitvec (n + i)) := unop (sign_extend  i n) 
def rotate_left  {n : Nat} (i : Nat) : term (bitvec n) -> term (bitvec n)       := unop (rotate_left  i n) 
def rotate_right {n : Nat} (i : Nat) : term (bitvec n) -> term (bitvec n)       := unop (rotate_right i n) 

def bvule        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvule n) 
def bvugt        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvugt n) 
def bvuge        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvuge n) 
def bvslt        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvslt n) 
def bvsle        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvsle n) 
def bvsgt        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvsgt n) 
def bvsge        {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := binop (bvsge n) 

-- Scripts and Commands
def script : Type := List command

structure SMTState :=
  (nextFreshId : Nat)
  (script      : script)

def smtM := StateM SMTState

instance : Monad smtM := inferInstanceAs (Monad (StateM SMTState))
instance : MonadState SMTState smtM := inferInstanceAs (MonadState SMTState (StateM SMTState))

def freshSymbol (base : String) : smtM String := do
  n <- modifyGet (fun st => (st.nextFreshId, { st with nextFreshId := st.nextFreshId + 1 }));
  pure ("|" ++ base ++ "-" ++ repr n ++ "|")

def runsmtM {a : Type} (next : Nat) (m : smtM a) : (a × (Nat × script)) := 
  let r := StateT.run m { nextFreshId := next, script := [] };
  (r.fst, (r.snd.nextFreshId, r.snd.script.reverse))

theorem const_sort_to_type_fold {res : sort} : forall {args : List sort}, 
 const_sort_to_type (List.foldr fsort (base res) args) = args_to_type args res -- := sorryAx _
| []       => rfl
| hd :: tl => congrArg (fun r => (term hd -> r)) (@const_sort_to_type_fold tl)

def declare_fun (s : String) (args : List sort) (res : sort) : smtM (args_to_type args res) := do
  s' <- freshSymbol s;  
  let ident := Raw.identifier.symbol (List.foldr fsort (base res) args) s';
  do modify (fun st => {st with script := (declare_fun s' args res) :: st.script });
     pure (Eq.mp const_sort_to_type_fold ident.expand_ident)

def inst_args_aux (res : sort) : 
    forall (args : List sort) (body : args_to_type args res) (acc : List (Sigma Raw.sorted_var)), 
    smtM (List (Sigma Raw.sorted_var) × term res) 
| [],       body, acc    => pure (acc.reverse, body)
| hd :: tl, f,    acc    => do   
  s <- freshSymbol "arg";  
  let arg := mk_symbol s hd;
  inst_args_aux tl (f arg) (Sigma.mk hd (Raw.sorted_var.mk hd s) :: acc)

def inst_args (res : sort) (args : List sort) (body : args_to_type args res) 
    : smtM (List (Sigma Raw.sorted_var) × term res) := 
    inst_args_aux res args body []

def define_fun (s : String) (args : List sort) (res : sort) (body : args_to_type args res)
  : smtM (args_to_type args res) := do
  s' <- freshSymbol s;
  let ident := Raw.identifier.symbol (List.foldr fsort (base res) args) s';
  (args', body') <- inst_args res args body;
  do modify (fun st => {st with script := (define_fun s' args' res body') :: st.script });
     pure (Eq.mp const_sort_to_type_fold ident.expand_ident)

-- Names the const if it is non-trivial, otherwise returns the original term
def name_term (name : String) : forall {s : sort} (tm : term s), smtM (term s)
-- FIXME
-- | ._, tm@(Raw.term.const _ _)     => pure tm
-- | ._, tm@(Raw.term.identifier _)  => pure tm
| s, tm                          => define_fun name [] s tm

def assert (b : term smt_bool) : smtM Unit := 
  modify (fun st => {st with script := (Raw.command.assert b) :: st.script })

def ex1 : smtM Unit :=
  do f <- declare_fun "f" [smt_bool, smt_bool] smt_bool;
     assert (f true false)

-- #check true
-- #check false
-- #eval toString (List.map toSExpr (runsmtM ex1))


end

end SMT
