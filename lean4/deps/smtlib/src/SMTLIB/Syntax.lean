-- Following the SMTLIB reference v2.6 

import Galois.Init.Nat

namespace SMTLIB

inductive sort : Type
| smt_bool : sort
| bitvec : Nat -> sort

namespace Raw
-- We use lowercase names for types to avoid clashing with Lean

def symbol := String

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
def to_string : spec_constant -> String
| numeral n   => toString n
| decimal n f => toString n ++ "." ++ toString f
| binary n v  => pp_hex n v
| string s    => "\"" ++ toString s ++ "\""

instance : HasToString spec_constant := ⟨spec_constant.to_string⟩

end spec_constant

inductive identifier : Type 
| symbol : symbol -> identifier
-- indexed symbols  

namespace identifier

def to_string : identifier -> String
| symbol s => s

instance : HasToString identifier := ⟨to_string⟩

end identifier

def mksexp (ss : List String) : String := "(" ++ ss.foldr (fun a s => a ++ " " ++ s) ")"

def sorted_var := symbol × sort
namespace sorted_var 

def to_string (s : sorted_var) : String := mksexp [s.fst, 

end sorted_var


-- S3.6
-- Use typed terms?
inductive term : Type
| spec_constant : spec_constant -> term
-- FIXME qual_identifier
| app_ident  : identifier -> List term -> term
| smt_let    : symbol -> term -> term -> term -- single binding only
| smt_forall : sorted_var -> term -> term
| smt_exists : sorted_var -> term -> term
-- FIXME match   
-- FIXME attribute

-- Theories.
-- * Core theory
| true     : term
| false    : term
| not      : term -> term
| impl     : term -> term -> term
| and      : term -> term -> term
| or       : term -> term -> term
| xor      : term -> term -> term
| eq       : term -> term -> term
| distinct : List term -> term -- without the list we get term explosion
| smt_ite  : term -> term -> term -> term

-- * BitVecs
-- hex/binary literals
| concat : Nat -> Nat -> term -> term -> term -- are the nats needed?
| extract : Nat -> Nat -> Nat -> term -> term
-- unops
| bvnot   : term -> term
| bvneg   : term -> term
-- binops
| bvand   : term -> term -> term
| bvor    : term -> term -> term
| bvadd   : term -> term -> term
| bvmul   : term -> term -> term
| bvudiv  : term -> term -> term
| bvurem  : term -> term -> term
| bvshl   : term -> term -> term
| bvlshr  : term -> term -> term
-- comparison
| bvult   : term -> term -> term

namespace term


#check (@term.recOn (fun _ => String) (fun _ => List String))

-- def to_string : term -> String
-- | spec_constant c  => toString c
-- | app_ident i args => mksexp (toString i :: list_to_string args)
-- | _ => ""


 -- ∀ (t : term),                                                                                                                                                 
 --    (∀ (a : spec_constant), (λ (_x : term), String) (spec_constant a)) →                                                                                        
 --    (∀ (a : identifier) (a_1 : List term), (λ (_x : List term), List String) a_1 → (λ (_x : term), String) (app_ident a a_1)) →                                 
 --    (∀ (a : symbol) (a_1a_2 : term), (λ (_x : term), String) a_1 → (λ (_x : term), String) a_2 → (λ (_x : term), String) (smt_let a a_1 a_2)) →
 --    (∀ (a : sorted_var) (a_1 : term), (λ (_x : term), String) a_1 → (λ (_x : term), String) (smt_forall a a_1)) →
 --    (∀ (a : sorted_var) (a_1 : term), (λ (_x : term), String) a_1 → (λ (_x : term), String) (smt_exists a a_1)) →
 --    (λ (_x : term), String) true →
 --    (λ (_x : term), String) false →
 --    (∀ (a : term), (λ (_x : term), String) a → (λ (_x : term), String) (not a)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (impl a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (and a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (or a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (xor a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (eq a a_1)) →
 --    (∀ (a : List term), (λ (_x : List term), List String) a → (λ (_x : term), String) (distinct a)) →
 --    (∀ (aa_1a_2 : term),
 --       (λ (_x : term), String) a →
 --       (λ (_x : term), String) a_1 → (λ (_x : term), String) a_2 → (λ (_x : term), String) (smt_ite a a_1 a_2)) →
 --    (∀ (aa_1 : Nat) (a_2a_3 : term), (λ (_x : term), String) a_2 → (λ (_x : term), String) a_3 → (λ (_x : term), String) (concat a a_1 a_2 a_3)) →
 --    (∀ (aa_1a_2 : Nat) (a_3 : term), (λ (_x : term), String) a_3 → (λ (_x : term), String) (extract a a_1 a_2 a_3)) →
 --    (∀ (a : term), (λ (_x : term), String) a → (λ (_x : term), String) (bvnot a)) →
 --    (∀ (a : term), (λ (_x : term), String) a → (λ (_x : term), String) (bvneg a)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvand a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvor a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvadd a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvmul a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvudiv a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvurem a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvshl a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvlshr a a_1)) →
 --    (∀ (aa_1 : term), (λ (_x : term), String) a → (λ (_x : term), String) a_1 → (λ (_x : term), String) (bvult a a_1)) →
--     (λ (_x : List term), List String) List.nil →
--     (∀ (hd : term) (tl : List term), (λ (_x : term), String) hd → (λ (_x : List term), List String) tl → (λ (_x : List term), List String) (hd::tl)) →
--     (λ (_x : term), String) t

-- -- things with lists in them are currently broken :(
-- def to_string (t : term) : String := 
--   @term.recOn (fun _ => String) (fun _ => List String)
--   (fun (x : spec_constant) => toString x)
--   (fun (i : identifier) (args : List term) (args_s : List String) => mksexp (toString i :: args))
--   (fun (v : symbol) (_ _ : term) (x : String) (body : String) => mksexp ["let", mksexp [v, x], body])
--   (fun (v : sorted_var) (_: term), (body : String)            => mksexp ["forall", mksexp [v, x], body])
--   (fun (v : sorted_var) (_: term), (body : String)            => mksexp ["exists", mksexp [v, x], body])
--   (




-- | smt_let    : symbol -> term -> term -> term -- single binding only
-- | smt_forall : sorted_var -> term -> term
-- | smt_exists : sorted_var -> term -> term
-- -- FIXME match   
-- -- FIXME attribute

-- -- Theories.
-- -- * Core theory
-- | true     : term
-- | false    : term
-- | not      : term -> term
-- | impl     : term -> term -> term
-- | and      : term -> term -> term
-- | or       : term -> term -> term
-- | xor      : term -> term -> term
-- | eq       : term -> term -> term
-- | distinct : List term -> term -- without the list we get term explosion
-- | smt_ite  : term -> term -> term -> term

-- -- * BitVecs
-- -- hex/binary literals
-- | concat : Nat -> Nat -> term -> term -> term -- are the nats needed?
-- | extract : Nat -> Nat -> Nat -> term -> term
-- -- unops
-- | bvnot   : term -> term
-- | bvneg   : term -> term
-- -- binops
-- | bvand   : term -> term -> term
-- | bvor    : term -> term -> term
-- | bvadd   : term -> term -> term
-- | bvmul   : term -> term -> term
-- | bvudiv  : term -> term -> term
-- | bvurem  : term -> term -> term
-- | bvshl   : term -> term -> term
-- | bvlshr  : term -> term -> term
-- -- comparison
-- | bvult   : term -> term -> term


end term



-- Scripts and Commands (S3.9)

inductive command : Type 
| assert : term -> command

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
| define_fun : symbol -> List sorted_var -> sort -> term -> command
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
open sort

-- *** Exported API ***

def term (s : sort) := Raw.term

def symbol := Raw.symbol

-- FIXME: we may want to include a proof of well-typedness here
def identifier (args : List sort) (result : sort) : Type := Raw.identifier

def args_to_type : List sort -> sort -> Type
| [], res        => term res
| (x :: xs), res => term x -> args_to_type xs res

-- given ident [a, b, c] and d, turns teram a -> term b -> term c -> term d into (ident [a, b, c])
def app_ident_aux (res : sort) (ident : Raw.identifier) : forall (args : List sort), List Raw.term -> args_to_type args res
| [], args        => Raw.term.app_ident ident args.reverse
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
