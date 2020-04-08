-- Following the SMTLIB reference v2.6 

import Galois.Init.Nat

namespace SExpr

def SExpr := String
def atom : String -> SExpr := id

protected
def SExpr.empty := "()"

class HasToSExpr (a : Type) := (toSExpr : a -> String)
open HasToSExpr


instance SExpr.HasToSExpr : HasToSExpr SExpr := ⟨id⟩

instance List.HasToSExpr {a : Type} [HasToSExpr a] : HasToSExpr (List a) :=
  ⟨fun ss => "(" ++ ss.foldr (fun a s => HasToSExpr.toSExpr a ++ " " ++ s ) ")"⟩

instance Nat.HasToSExpr : HasToSExpr Nat := ⟨toString⟩

instance String.HasToSExpr : HasToSExpr String := ⟨fun s => "\"" ++ s ++ "\""⟩

protected
def app (f : SExpr) (args : List SExpr) : SExpr := toSExpr (f :: args)

end SExpr

namespace SMTLIB

open SExpr
open SExpr.HasToSExpr

-- SMTLIB specific sexpr stuff
def indexed (f : SExpr) (args : List SExpr) : SExpr :=
  SExpr.app (atom "_") (f :: args)

inductive sort : Type
| smt_bool : sort
| bitvec : Nat -> sort

-- Basically a list.
inductive funsort : Type 
| base  : sort -> funsort
| fsort : sort -> funsort -> funsort

open sort

namespace sort

protected
def to_sexpr : sort -> SExpr
| smt_bool => atom "Bool"
| bitvec n => indexed (atom "BitVec") [toSExpr n]

instance : HasToSExpr sort := ⟨sort.to_sexpr⟩
          
end sort

structure const_sort :=
  (args : List sort)
  (result : sort) 

namespace const_sort 

def smt_bool := const_sort.mk [] sort.smt_bool
def bitvec (n : Nat) := const_sort.mk [] (sort.bitvec n)

end const_sort

namespace Raw
-- We use lowercase names for types to avoid clashing with Lean

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

protected def to_hex_with_leading_zeros : List Char → Nat → Nat → String
| prev, 0, _ => prev.asString
| prev, (Nat.succ w), x =>
  let c := (Nat.land x 0xf).digitChar;
  to_hex_with_leading_zeros (c::prev) w (Nat.shiftr x 4)

--- Print word as hex
def pp_hex (n : Nat) (v : Nat) : String := 
  "0x" ++ spec_constant.to_hex_with_leading_zeros [] (n / 4) v

end to_hex

protected
def to_sexpr : spec_constant -> SExpr
| numeral n   => toSExpr n
| decimal n f => atom (toString n ++ "." ++ toString f)
| binary n v  => atom (pp_hex n v)
| string s    => toSExpr s

instance : HasToSExpr spec_constant := ⟨spec_constant.to_sexpr⟩

end spec_constant

-- distinct is a term as it has arbitrary arity
inductive builtin_identifier : const_sort -> Type
-- * Core theory
| true                : builtin_identifier const_sort.smt_bool
| false               : builtin_identifier const_sort.smt_bool
| not                 : builtin_identifier (const_sort.mk [smt_bool] smt_bool)
| impl                : builtin_identifier (const_sort.mk [smt_bool, smt_bool] smt_bool)
| and                 : builtin_identifier (const_sort.mk [smt_bool, smt_bool] smt_bool)
| or                  : builtin_identifier (const_sort.mk [smt_bool, smt_bool] smt_bool)
| xor                 : builtin_identifier (const_sort.mk [smt_bool, smt_bool] smt_bool)
| eq       (s : sort) : builtin_identifier (const_sort.mk [s, s] smt_bool)
| smt_ite  (s : sort) : builtin_identifier (const_sort.mk [smt_bool, s, s] s)
| distinct (s : sort) (arity : Nat)
                      : builtin_identifier (const_sort.mk (List.replicate arity s) smt_bool
)-- * BitVecs
-- hex/binary literals
| concat  (n : Nat) (m : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec m] (bitvec (n + m)))
| extract (n : Nat) (i : Nat) (j : Nat) : builtin_identifier (const_sort.mk [bitvec n] (bitvec (i - j + 1)))
-- -- unops
| bvnot   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n] (bitvec n))
| bvneg   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n] (bitvec n))
-- -- binops
| bvand   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvor    (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvadd   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvmul   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvudiv  (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvurem  (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvshl   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
| bvlshr  (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] (bitvec n))
-- -- comparison
| bvult   (n : Nat) : builtin_identifier (const_sort.mk [bitvec n, bitvec n] smt_bool)

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
-- * BitVecs
-- hex/binary literals
| _, concat _ _           => atom "concat"
| _, extract _ _ _        => atom "extract"
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

inductive sorted_list (f : sort -> Type) : List sort -> Type 
| nil  : sorted_list []
| cons {s : sort} {ss : List sort} : f s -> sorted_list ss -> sorted_list (s :: ss)

-- S3.6
-- Use typed terms?
inductive term : sort -> Type
| const (s : sort) : spec_constant -> term s
| app_ident {cs : const_sort} : identifier cs -> sorted_list term cs.args -> term cs.result
| smt_let {s t : sort}        : symbol -> term t -> term s -> term s -- single binding only
| smt_forall {s : sort} : sorted_var s -> term smt_bool -> term smt_bool
| smt_exists {s : sort} : sorted_var s -> term smt_bool -> term smt_bool

namespace term

  -- ∀ {a : sort} (t : term a),
  --   (∀ (s : sort) (a : spec_constant), (λ (_x : sort) (_x : term _x), SExpr) s (spec_constant s a)) →
  --   (∀ {cs : const_sort} (a : identifier cs) (a_1 : sorted_list term (cs.args)),
  --      (λ (_x : List sort) (_x : sorted_list term _x), List SExpr) (cs.args) a_1 →
  --      (λ (_x : sort) (_x : term _x), SExpr) (cs.result) (app_ident a a_1)) →
  --   (∀ {st : sort} (a : symbol) (a_1 : term t) (a_2 : term s),
  --      (λ (_x : sort) (_x : term _x), SExpr) t a_1 →
  --      (λ (_x : sort) (_x : term _x), SExpr) s a_2 → (λ (_x : sort) (_x : term _x), SExpr) s (smt_let a a_1 a_2)) →
  --   (∀ {s : sort} (a : sorted_var s) (a_1 : term smt_bool), (λ (_x : sort) (_x : term _x), SExpr) smt_bool a_1 → (λ (_x : sort) (_x : term _x), SExpr) smt_bool (smt_forall a a_1)) →
  --   (∀ {s : sort} (a : sorted_var s) (a_1 : term smt_bool), (λ (_x : sort) (_x : term _x), SExpr) smt_bool a_1 → (λ (_x : sort) (_x : term _x), SExpr) smt_bool (smt_exists a a_1)) →
  --   (λ (_x : List sort) (_x : sorted_list term _x), List SExpr) List.nil (sorted_list.nil term) →
  --   (∀ {s : sort} {ss : List sort} (a : term s) (a_1 : sorted_list term ss),
  --      (λ (_x : sort) (_x : term _x), SExpr) s a →
  --      (λ (_x : List sort) (_x : sorted_list term _x), List SExpr) ss a_1 →
  --      (λ (_x : List sort) (_x : sorted_list term _x), List SExpr) (s::ss) (sorted_list.cons a a_1)) →
  --   (λ (_x : sort) (_x : term _x), SExpr) a t


-- things with lists in them are currently broken :(
def to_sexpr {s : sort} (t : term s) : SExpr := 
  @term.recOn (fun _ _ => SExpr) (fun _ _ => List SExpr) s t
  (fun (s : sort) (x : spec_constant) => toSExpr x) -- include sort here?
  (fun (cs : const_sort) (i : identifier cs) (_args : sorted_list term cs.args) (args_s : List SExpr) => SExpr.app (toSExpr i) args_s)
  (fun {s t : sort} (v : symbol) (_ : term t) (_ : term s) (x : SExpr) (body : SExpr) => toSExpr [atom "let", toSExpr [toSExpr v, x], body])
  (fun {s : sort} (v : sorted_var s) (_: term smt_bool) (body : SExpr)                => SExpr.app (atom "forall") [toSExpr [toSExpr v], body])
  (fun {s : sort} (v : sorted_var s) (_: term smt_bool) (body : SExpr)                => SExpr.app (atom "exists") [toSExpr [toSExpr v], body])
  -- lists
  []
  (fun {s : sort} {ss : List sort} (_ : term s) (_ : sorted_list term ss) (x : SExpr) (xs : List SExpr) => x :: xs)

end term



-- Scripts and Commands (S3.9)

inductive command : Type 
| assert : term smt_bool -> command

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
| define_fun {ss : List sort} : symbol -> sorted_list sorted_var ss 
                              -> forall (s : sort), term s -> command

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

-- def toString : command -> String 
-- | assert 

end command

end Raw


-- *** Exported API ***

def term := Raw.term

def symbol := Raw.symbol

def identifier := Raw.identifier

def args_to_type : List sort -> sort -> Type
| [], res        => term res
| (x :: xs), res => term x -> args_to_type xs res

-- given ident [a, b, c] and d, turns teram a -> term b -> term c -> term d into (ident [a, b, c])
def app_ident_aux (cs : const_sort) (ident : identifier cs) 
  : sorted_list term cs.args -> args_to_type cs.args cs.result
| nil             => Raw.term.app_ident ident args.reverse
| (s :: ss), args => fun (t_s : term s) => app_ident_aux ss (t_s :: args)

def app_ident  {args : List sort} {res : sort} (ident : identifier args res) : args_to_type args res
  := app_ident_aux res ident args []

-- Builtin terms
def true  : term smt_bool                           := Raw.term.true
def false : term smt_bool                           := Raw.term.false
def not   : term smt_bool -> term smt_bool              := Raw.term.not
def impl  : term smt_bool -> term smt_bool -> term smt_bool := Raw.term.impl
def and   : term smt_bool -> term smt_bool -> term smt_bool := Raw.term.and
def or    : term smt_bool -> term smt_bool -> term smt_bool := Raw.term.or
def xor   : term smt_bool -> term smt_bool -> term smt_bool := Raw.term.xor
def eq {a : sort} : term a -> term a -> term smt_bool := Raw.term.eq
def distinct {a : sort} : List (term a) -> term smt_bool := Raw.term.distinct
def smt_ite  {a : sort} : term smt_bool -> term a -> term a -> term a := Raw.term.smt_ite

-- BitVecs
-- hex/binary literals
def concat {n m : Nat} : term (bitvec n) -> term (bitvec m) -> term (bitvec (n + m)) := Raw.term.concat n m
def extract {n : Nat} (i : Nat) (j : Nat) : term (bitvec n) -> term (bitvec (i - j + 1)) := Raw.term.extract n i j
def bvnot {n : Nat} : term (bitvec n) -> term (bitvec n) := Raw.term.bvnot
def bvneg {n : Nat} : term (bitvec n) -> term (bitvec n) := Raw.term.bvneg

-- binops
def bvand {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvand
def bvor  {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvor
def bvadd {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvadd
def bvmul {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvmul
def bvudiv {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvudiv
def bvurem {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvurem
def bvshl {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvshl
def bvlshr {n : Nat} : term (bitvec n) -> term (bitvec n) -> term (bitvec n) := Raw.term.bvlshr
-- comparison
def bvult {n : Nat} : term (bitvec n) -> term (bitvec n) -> term smt_bool := Raw.term.bvult

-- Scripts and Commands
def script : Type := List Raw.command
def smtM := StateM script

instance : Monad smtM := inferInstanceAs (Monad (StateM script))
instance : MonadState script smtM := inferInstanceAs (MonadState script (StateM script))

def runsmtM {a : Type} (m : smtM a) : script := (StateT.run m []).snd

-- FIXME: check that s is new etc. 
def declare_fun (s : symbol) (args : List sort) (res : sort) : smtM (args_to_type args res) :=
  let ident : identifier args res := Raw.identifier.symbol s;
  do modify (fun st => (Raw.command.declare_fun s args res) :: st);
     pure (app_ident ident)


end SMTLIB
