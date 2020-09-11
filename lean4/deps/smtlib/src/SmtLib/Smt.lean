
-- import Galois.Init.Nat
-- import Galois.Data.List
-- import Galois.Data.SExp
import Galois.Data.SExp
import SmtLib.Syntax
import SmtLib.IdGen



export SExpr.HasToSExpr (toSExpr)
export Smt.IdGen


namespace Smt

open SExpr
open SmtSort

export Smt 
(SmtSort.bool
 SmtSort.bitvec
 SmtSort.array
 SmtSort.bv8
 SmtSort.bv16
 SmtSort.bv32
 SmtSort.bv64)
--export SmtSort (bool bitvec array)

-- *** Exported API ***


def Term (s : SmtSort) := Raw.Term (Raw.ConstSort.base s)
instance Term.HasToSExpr (s : SmtSort) : HasToSExpr (Term s) := 
  inferInstanceAs (HasToSExpr (Raw.Term (Raw.ConstSort.base s)))

def Symbol := Raw.Symbol

@[reducible]
def  Command := Raw.Command

def Logic := Raw.Logic
namespace Logic
def all : Logic := Raw.Logic.all
end Logic


def Opt := Raw.Opt
namespace Opt
def produceModels : Bool → Opt := Raw.Opt.produceModels
end Opt

namespace Command

def assert (b : Term bool) : Command := 
  Raw.Command.assert b
def comment (content : String) : Command :=
  Raw.Command.comment content
def setLogic (l : Logic) : Command :=
  Raw.Command.setLogic l
def setOption (o : Opt) : Command :=
  Raw.Command.setOption o
def setProduceModels (b : Bool) : Command :=
  Raw.Command.setOption (Opt.produceModels b)
def checkSatAssuming (bs : List (Term bool)) : Command :=
  Raw.Command.checkSatAssuming bs
def exit : Command :=
  Raw.Command.exit

end Command


-- def Ident := Raw.Ident

@[reducible]
def funType (domain : List SmtSort) (codomain : SmtSort) : Type
  := List.foldr (fun x t => Term x -> t) (Term codomain) domain
-- | [], res        => Term res
-- | (x :: xs), res => Term x -> funType xs res

-- -- given ident [a, b, c] and d, turns teram a -> Term b -> Term c -> Term d into (ident [a, b, c])
-- def app_ident_aux (cs : ConstSort) (ident : Ident cs) 
--   : sorted_list Term cs.args -> funType cs.args cs.result
-- | nil             => Raw.Term.app_ident ident args.reverse
-- | (s :: ss), args => fun (t_s : Term s) => app_ident_aux ss (t_s :: args)

-- def app_ident  {args : List sort} {res : sort} (ident : Ident args res) : funType args res
--   := app_ident_aux res ident args []

section
open Raw.Term
open Raw.BuiltinIdent
open Raw.Ident
open Raw.Command
open Raw (ConstSort)
open Raw.ConstSort (fsort base)
open Raw (SpecConst)
open Raw.SpecConst

def ConstSortToType : ConstSort -> Type 
| base s    => Term s
| fsort s t => Term s -> ConstSortToType t


def mkSymbol (sym : Symbol) (s : SmtSort) : Term s := 
  Raw.Term.ident (Raw.Ident.symbol (Raw.ConstSort.base s) sym)  


namespace Raw.Ident

-- inductive sorted_list (f : sort -> Type) : List sort -> Type 
-- | nil  : sorted_list []
-- | cons {s : sort} {ss : List sort} : f s -> sorted_list ss -> sorted_list (s :: ss)

protected
def expandIdentAux : forall {cs : ConstSort}, Raw.Term cs -> ConstSortToType cs
| base s, i    => i
| fsort s t, i => fun x => expandIdentAux (app i x)

def expandIdent {cs : ConstSort} (i : Raw.Ident cs) : ConstSortToType cs :=
  Raw.Ident.expandIdentAux (ident i)

end Raw.Ident

private
def unop {s t : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.unop s t)) (a : Term s)
  : Term t := app (ident (builtin i)) a

private
def binop {a b c : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.binop a b c)) 
          (x : Term a) (y : Term b) : Term c := app (app (ident (builtin i)) x) y

private
def ternop {a b c d : SmtSort} 
           (i : Raw.BuiltinIdent (Raw.BuiltinIdent.ternop a b c d))
           (x : Term a) (y : Term b) (z : Term c) : Term d 
           := app (app (app (ident (builtin i)) x) y) z

private
def quadop {a b c d e : SmtSort} 
           (i : Raw.BuiltinIdent (Raw.BuiltinIdent.quadop a b c d e))
           (w : Term a) (x : Term b) (y : Term c) (z : Term d) : Term e
           := app (app (app (app (ident (builtin i)) w) x) y) z

-- Builtin terms
def true  : Term bool                           := ident (builtin true)
def false : Term bool                           := ident (builtin false)
def not   : Term bool -> Term bool          := unop not
def impl  : Term bool -> Term bool -> Term bool := binop impl
def and   : Term bool -> Term bool -> Term bool := binop and
def or    : Term bool -> Term bool -> Term bool := binop or
def xor   : Term bool -> Term bool -> Term bool := binop xor
def eq {a : SmtSort} : Term a -> Term a -> Term bool       := binop (eq a)
-- FIXME
-- def distinct {a : SmtSort} : List (Term a) -> Term bool := Raw.Term.distinct
def smtIte  {a : SmtSort} : Term bool -> Term a -> Term a -> Term a := ternop (smtIte a)

-- Arrays
def select (k v : SmtSort) : Term (array k v) -> Term k -> Term v :=
  binop (select k v)

def store  (k v : SmtSort) : Term (array k v) -> Term k -> Term v -> Term (array k v) :=
  ternop (store k v)

def eqrange  {k : RangeSort} {v : SmtSort} : Term (array k.sort v) -> Term (array k.sort v) -> Term k.sort -> Term k.sort -> Term bool
    := quadop (eqrange k v)

-- BitVecs
-- hex/binary literals
def bvimm (n v : Nat) : Term (bitvec n) := const (bitvec n) (binary n v)
-- c.f. bitvec.of_int 
def bvimm' (n : Nat) : Int -> Term (bitvec n)
| Int.ofNat x   => bvimm n x
| Int.negSucc x => bvimm n (Nat.ldiff (2^n-1) x)

def bvAsConst {n : Nat} : Term (bitvec n) -> Option Nat 
| const _ (binary _ v) => some v
| _                    => none

def concat {n m : Nat} : Term (bitvec n) -> Term (bitvec m) -> Term (bitvec (n + m)) := 
  binop (concat n m)
def extract {n : Nat} (i : Nat) (j : Nat) : Term (bitvec n) -> Term (bitvec (i + 1 - j)) :=
  unop (extract n i j)
def bvnot {n : Nat} : Term (bitvec n) -> Term (bitvec n) := unop (bvnot n)
def bvneg {n : Nat} : Term (bitvec n) -> Term (bitvec n) := unop (bvneg n)

-- binops
def bvand {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvand  n)
def bvor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvor   n)
def bvadd {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvadd  n)
def bvmul {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvmul  n)
def bvudiv {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvudiv n)
def bvurem {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvurem n)
def bvshl {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvshl  n)
def bvlshr {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvlshr n)
-- comparison
def bvult {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvult n)


-- Functions defined by Smt as abbrevs.
def bvnand {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvnand n) 
def bvnor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvnor  n) 
def bvxor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvxor  n) 
def bvxnor {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvxnor n) 
def bvcomp {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec 1)  := binop (bvcomp n)
def bvsub  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsub  n) 
def bvsdiv {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsdiv n) 
def bvsrem {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsrem n) 
def bvsmod {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsmod n) 
def bvashr {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvashr n) 

-- Defined, param by i >= 1
def repeat {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (i * n)) := unop (repeat i n)

-- Defined, param by i >= 0
def zeroExtend  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (n + i)) := unop (zeroExtend  i n) 
def signExtend  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (n + i)) := unop (signExtend  i n) 
def rotateLeft  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec n)       := unop (rotateLeft  i n) 
def rotateRight {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec n)       := unop (rotateRight i n) 

def bvule        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvule n) 
def bvugt        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvugt n) 
def bvuge        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvuge n) 
def bvslt        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvslt n) 
def bvsle        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsle n) 
def bvsgt        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsgt n) 
def bvsge        {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsge n) 

-- Pure version, doesn't touch the symbol name
def smtLet {s t : SmtSort} (v : Symbol) (e : Term s) (body : Term s -> Term t) : Term t :=
  let v_e := mkSymbol v s;
  Raw.Term.smtLet v e (body v_e)

-- Scripts and Commands
def Script : Type := List Command

namespace Script

instance : HasAppend Smt.Script :=
inferInstanceAs (HasAppend (List Command))

end Script

structure SmtState :=
  (idGen  : IdGen)
  (revScript : Script)

def SmtM := StateM SmtState

instance : Monad SmtM := inferInstanceAs (Monad (StateM SmtState))
instance : MonadStateOf SmtState SmtM := inferInstanceAs (MonadStateOf SmtState (StateM SmtState))

/-- Generate a fresh symbol in the monad, if possible simply using the suggested string.  --/
def freshSymbol (suggestedStr : String) : SmtM String := do
  (idGen', sym) ← (λ (g:IdGen) => g.genId suggestedStr) <$> SmtState.idGen <$> get;
  modify (λ s => {s with idGen := idGen'});
  pure sym

def runSmtM {a : Type} (idGen : IdGen) (m : SmtM a) : (a × IdGen × Script) :=
  let r := StateT.run m { idGen := idGen, revScript := [] };
  (r.fst, (r.snd.idGen, r.snd.revScript.reverse))

theorem ConstSortToTypeFold {res : SmtSort} : forall {args : List SmtSort}, 
 ConstSortToType (List.foldr fsort (base res) args) = funType args res -- := sorryAx _
| []       => rfl
| hd :: tl => congrArg (fun r => (Term hd -> r)) (@ConstSortToTypeFold tl)

def declareFun (s : String) (args : List SmtSort) (res : SmtSort) : SmtM (funType args res) := do
  s' <- freshSymbol s;
  let ident := Raw.Ident.symbol (List.foldr fsort (base res) args) s';
  do modify (fun st => {st with revScript := (declareFun s' args res) :: st.revScript });
     pure (Eq.mp ConstSortToTypeFold ident.expandIdent)

def instArgsAux (res : SmtSort) : 
    forall (args : List SmtSort) (body : funType args res) (acc : List (Sigma Raw.SortedVar)), 
    SmtM (List (Sigma Raw.SortedVar) × Term res) 
| [],       body, acc    => pure (acc.reverse, body)
| hd :: tl, f,    acc    => do   
  s <- freshSymbol "arg";  
  let arg := mkSymbol s hd;
  instArgsAux tl (f arg) (Sigma.mk hd (Raw.SortedVar.mk s) :: acc)

def instArgs (res : SmtSort) (args : List SmtSort) (body : funType args res)
    : SmtM (List (Sigma Raw.SortedVar) × Term res) :=
    instArgsAux res args body []

def defineFun (s : String) (args : List SmtSort) (res : SmtSort) (body : funType args res)
  : SmtM (funType args res) := do
  s' <- freshSymbol s;
  let ident := Raw.Ident.symbol (List.foldr fsort (base res) args) s';
  (args', body') <- instArgs res args body;
  do modify (fun st => {st with revScript := (defineFun s' args' res body') :: st.revScript });
     pure (Eq.mp ConstSortToTypeFold ident.expandIdent)

def isAtomic : forall {s : ConstSort}, Raw.Term s -> Bool
| _, Raw.Term.const _ _      => Bool.true
| _, Raw.Term.ident      _   => Bool.true
| _, Raw.Term.app _ _        => Bool.false
| _, Raw.Term.smtLet _ _ _  => Bool.false
| _, Raw.Term.smtForall _ _ => Bool.false
| _, Raw.Term.smtExists _ _ => Bool.false

-- Names the const if it is non-trivial, otherwise returns the original Term
def nameTerm (name : String) {s : SmtSort} (tm : Term s) : SmtM (Term s) :=
  if isAtomic tm then pure tm else  defineFun name [] s tm





def assert (b : Term bool) : SmtM Unit := 
  modify (fun st => {st with revScript := (Command.assert b) :: st.revScript })
def comment (content : String) : SmtM Unit :=
  modify (fun st => {st with revScript := (Command.comment content) :: st.revScript })
def setLogic (l : Logic) : SmtM Unit :=
  modify (fun st => {st with revScript := (Command.setLogic l) :: st.revScript })
def setOption (o : Opt) : SmtM Unit :=
  modify (fun st => {st with revScript := (Command.setOption o) :: st.revScript })
def setProduceModels (b : Bool) : SmtM Unit :=
  modify (fun st => {st with revScript := (Command.setOption (Raw.Opt.produceModels b)) :: st.revScript})
def checkSatAssuming (bs : List (Term bool)) : SmtM Unit :=
  modify (fun st => {st with revScript := (Command.checkSatAssuming bs) :: st.revScript })
def exit : SmtM Unit :=
  modify (fun st => {st with revScript := Command.exit :: st.revScript })


def liftCommand (c : Command) : SmtM Unit :=
  modify (fun st => {st with revScript := c :: st.revScript })


inductive CheckSatResult
| sat : CheckSatResult
| unsat : CheckSatResult
| unknown : CheckSatResult
| unsupported : CheckSatResult
| unrecognized : String → CheckSatResult

def parseCheckSatResult (rawStr : String) : CheckSatResult :=
match rawStr.trim with
| "sat" => CheckSatResult.sat
| "unsat" => CheckSatResult.unsat
| "unknown" => CheckSatResult.unknown
| "unsupported" => CheckSatResult.unsupported
| other => CheckSatResult.unrecognized other

-- #check true
-- #check false
-- #eval toString (List.map toSExpr (runSmtM ex1))

/-- Converts a command to a string terminated by a newline.--/
def Command.toLine (c:Command) : String :=
let cStr := (WellFormedSExp.SExp.toString (toSExpr c));
if c.isComment
then cStr
else cStr ++ "\n"

end


-- --------------------------------------------------------------------------------

-- def smtM : (Env -> Type) -> Type := ...

-- structure Term (s : Sort) (e : Env) :=
--   ( term : Raw.Term s)
--   ( wf : WellSorted e term )

-- def PairF {s : Type} : (s -> Type) -> (s -> Type) -> (s -> Type)


-- @PairF Env (Term s1) (Term s2)


-- structure SMTContext :=
--   ( decls   : RBMap Symbol ConstSort ) 
--   ( defs    : RBMap Symbol (Sigma Raw.Term) )
--   ( defsWF  : decls ++ g desf |- free defs )
--   ( acyclic : acyclic defs )
--   ( asserts : [ Raw.Term smt_bool ] )

-- def ContextEnv : SMTContext -> RBMap Symbol ConstSort := ... union decls defs

-- def assert : smtM (Term smt_bool) -> smtM UnitF

-- def property : smtM UnitF -> Prop

-- class Monotone F :=
--   ( apply : Morphism e e' -> F e -> F e' )

-- instance Monotone (Term s) := ...

-- instance Monotone [Monotone f] [Monotone g] (PairF f g) :=
--   ...

-- def declare [ Monotone F ] : Symbol -> sort -> smtM F -> smtM (PairF F (Term s))


-- def myExample : smtM (PairF (Term (bv 64)) (Term (bv 32))) :=
--   declare "std2" (bv 32) $ 
--   declare "std1" (bv 64) smtM.empty
  

-- def fmapF : (forall e, a e -> b e) -> smtM a -> smtM b

-- def StdLib e = { std1 : Term e ..., std2 : Term e ... } 

-- def mkStdLib : PairF (Term (bv 32)) (PairF (Term (bv 64)) ...) -> StdLib


-- -- G e 
-- -- F e' 
-- -- ==> 
-- -- F (e' ++ e) (G (e' ++ e))

-- def <*> [ Monotone G ] [ Monotone F] : stmM F -> smtM G -> smtM (appF F G)

-- -- SMT.eq <$F> declare ""

-- --------------------------------------------------------------------------------

-- def smtM : (Env -> Type) -> (Env -> Type) -> Type :=

-- ... smtM StdLib (Term (bv 32)) ... 





-- --------------------------------------------------------------------------------

-- def smtM (e : Env) : Type -> Type := ...

-- def bind : smtM e a -> (a -> smtM e b) -> smtM e b

-- -- def bind' : smtM e a -> (a -> smtM e' b) -> smtM e' b

-- def assert : Term smt_sort e -> smtM e Unit

-- def declare {e : Env} (sym : Symbol) (s : smt_sort) : (Morphism e (s :: e) -> Term (s :: e) s -> smtM (s :: e) a) -> smtM (s :: e) a

-- def makeSmtM : smtM [] Unit


-- def myExample :=
--   @declare [] "std1" (bv 64) $ fun _morph (std1tm : Term [bv64] (bv 64))-> 
--     declare "std2" (bv 32)  $ fun morph (std2tm : Term [bv 32, bv 64] (bv 32)) -> 
--       let std1tm' := morph.apply std1tm;
--       let ctx := mkPairF std1tm' std2tm' ;
--       define "foo" _ (SMT.eq std1 std2) 

-- --------------------------------------------------------------------------------

-- def semantics : Model -> Script -> Prop

-- def denotation (s : Script) : Prop :=
--   forall M, M ~ s.decls -> semantics M s

-- def soundness : not (exists M, semantics M s) -> not (denotation s) :=
--   fun H : denotation s =>
--     unfold H to get (forall M, M ~ s.decls -> semantics M s ) (1) 
--     get an M s.t. M ~ s.decls
--     hence semantics M s from (1)
--     however
--     not (exists M, semantics M s)
--     hence f (exists M, semantics M s -> False)
--     hence False


      
   
  
  
  








end Smt
