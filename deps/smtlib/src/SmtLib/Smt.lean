
-- import Galois.Init.Nat
-- import Galois.Data.List
-- import Galois.Data.SExp
import Galois.Data.SExp
import SmtLib.Syntax
import SmtLib.IdGen

-- For smart constuctors
import SmtLib.Denote.BuiltinId
import SmtLib.Denote.Term

export SExpr.ToSExpr (toSExpr)
export Smt (IdGen)


namespace Smt

open SExpr
open SmtSort

export SmtSort ( bool
                 bitvec
                 tuple
                 array
                 bv8
                 bv16
                 bv32
                 bv64
               )

-- *** Exported API ***


def Term (s : SmtSort) := Raw.Term (Raw.ConstSort.base s)

instance (s : SmtSort) : ToSExpr (Term s) := 
  inferInstanceAs (ToSExpr (Raw.Term (Raw.ConstSort.base s)))

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
open Raw (Literal)
open Raw.Literal

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
| fsort s t, i => fun x => Ident.expandIdentAux (app i x)

def expandIdent {cs : ConstSort} (i : Raw.Ident cs) : ConstSortToType cs :=
  Raw.Ident.expandIdentAux (ident i)

end Raw.Ident

-- Non-simplifying constructors
private
def unop' {s t : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.unop s t)) (a : Term s)
          :  Term t  := app (ident (builtin i)) a

private
def binop' {a b c : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.binop a b c)) 
          (x : Term a) (y : Term b) : Term c := app (app (ident (builtin i)) x) y

private
def ternop' {a b c d : SmtSort} 
           (i : Raw.BuiltinIdent (Raw.BuiltinIdent.ternop a b c d))
           (x : Term a) (y : Term b) (z : Term c) : Term d 
           := app (app (app (ident (builtin i)) x) y) z

private
def quadop' {a b c d e : SmtSort} 
           (i : Raw.BuiltinIdent (Raw.BuiltinIdent.quadop a b c d e))
           (w : Term a) (x : Term b) (y : Term c) (z : Term d) : Term e
           := app (app (app (app (ident (builtin i)) w) x) y) z

-- Builtin terms
protected def true  : Term bool := const _ (boolean true)
protected def false : Term bool := const _ (boolean false)

namespace SmtSort

-- def default : forall (s : SmtSort), Term s
--   | bool        => Smt.false
--   | bitvec n    => const _ (binary n 0)
--   | array k v   => app (ident (builtin (arrayConst k v))) v.default
--   | tuple s1 s2 => app (app (ident (builtin (mkTuple s1 s2))) s1.default) s2.default

def undenote : forall (s : SmtSort), s.denote.type -> Term s 
  | bool, b        => if b then Smt.true else Smt.false
  | bitvec n, bv   => const _ (binary n (bitvec.to_nat bv))
  | array k v, arr => List.foldl (fun t el => ternop' (store k v) t (undenote k el.fst) (undenote v el.snd))
                                 (unop' (arrayConst k v) (undenote v arr.val.default))
                                 arr.val.entries
  | tuple s1 s2, p => binop' (mkTuple s1 s2) (undenote s1 p.fst) (undenote s2 p.snd)

end SmtSort

private
def unop : forall {s t : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.unop s t)) (a : Term s)
         ,  Term t
  | s, t, i, const _ sc => t.undenote (Raw.BuiltinIdent.denote _ i sc.semantics)
  | s, t, i, a          => unop' i a

private
def binop : forall {a b c : SmtSort} (i : Raw.BuiltinIdent (Raw.BuiltinIdent.binop a b c)) 
            (x : Term a) (y : Term b) , Term c
  | _, _, c, i, const _ cx, const _ cy => c.undenote (Raw.BuiltinIdent.denote _ i cx.semantics cy.semantics)
  | _, _, _, i, x, y => binop' i x y

private
def ternop : forall {a b c d : SmtSort} 
             (i : Raw.BuiltinIdent (Raw.BuiltinIdent.ternop a b c d))
             (x : Term a) (y : Term b) (z : Term c), Term d 
  | _, _, _, c, i, const _ cx, const _ cy, const _ cz => 
    c.undenote (Raw.BuiltinIdent.denote _ i cx.semantics cy.semantics cz.semantics)
  | _, _, _, _, i, x, y, z => ternop' i x y z

private
def quadop : forall {a b c d e : SmtSort} 
             (i : Raw.BuiltinIdent (Raw.BuiltinIdent.quadop a b c d e))
             (w : Term a) (x : Term b) (y : Term c) (z : Term d), Term e
  | _, _, _, _, c, i, const _ cw, const _ cx, const _ cy, const _ cz => 
    c.undenote (Raw.BuiltinIdent.denote _ i cw.semantics cx.semantics cy.semantics cz.semantics)
  | _, _, _, _, _, i, w, x, y, z => quadop' i w x y z

protected def not   : Term bool -> Term bool := unop not
protected def impl  : Term bool -> Term bool -> Term bool := binop impl
protected def and   : Term bool -> Term bool -> Term bool := binop and
protected def or    : Term bool -> Term bool -> Term bool := binop or
protected def xor   : Term bool -> Term bool -> Term bool := binop xor
protected def eq {a : SmtSort} : Term a -> Term a -> Term bool       := binop (eq a)
-- FIXME
-- def distinct {a : SmtSort} : List (Term a) -> Term bool := Raw.Term.distinct

protected def smtIte  {a : SmtSort} : Term bool -> Term a -> Term a -> Term a 
  -- FIXME: verify that this is OK
  | const _ (boolean b), t, f => if b then t else f
  | c, t, f                   => ternop (smtIte a) c t f

-- Derived helpers
private def allAux : Term bool → List (Term bool) → Term bool
| p, [] => p
| p, q::qs => allAux (Smt.and p q) qs

def all : List (Term bool) → Term bool
| [] => Smt.true
| p::ps => allAux p ps

private def anyAux : Term bool → List (Term bool) → Term bool
| p, [] => p
| p, q::qs => anyAux (Smt.or p q) qs

def any : List (Term bool) → Term bool
| [] => Smt.false
| p::ps => anyAux p ps

-- Tuples

protected
def fst (a b : SmtSort) : Term (tuple a b) -> Term a := unop (fst a b)

protected
def snd (a b : SmtSort) : Term (tuple a b) -> Term b := unop (snd a b)

protected
def mkTuple (a b : SmtSort) : Term a -> Term b -> Term (tuple a b) := binop (mkTuple a b)

-- Arrays
protected
def arrayConst (k v : SmtSort) : Term v -> Term (array k v) := unop (arrayConst k v) 

protected
def select (k v : SmtSort) : Term (array k v) -> Term k -> Term v :=
  binop (select k v)

protected
def store  (k v : SmtSort) : Term (array k v) -> Term k -> Term v -> Term (array k v) :=
  ternop (store k v)

protected
def eqrange  {k : RangeSort} {v : SmtSort} : Term (array k.sort v) -> Term (array k.sort v) -> Term k.sort -> Term k.sort -> Term bool
    := quadop (eqrange k v)

-- BitVecs
-- hex/binary literals
def bvimm (width val : Nat) : Term (bitvec width) := 
const (bitvec width) (binary width val)

-- c.f. bitvec.of_int 
def bvimm' (width : Nat) : Int -> Term (bitvec width)
| Int.ofNat x   => bvimm width x
| Int.negSucc x => bvimm width (Nat.ldiff (2^width-1) x)

def bvAsConst {n : Nat} : Term (bitvec n) -> Option Nat 
| const _ (binary _ v) => some v
| _                    => none

protected
def concat {n m : Nat} : Term (bitvec n) -> Term (bitvec m) -> Term (bitvec (n + m)) := 
  binop (concat n m)

protected
def extract {n : Nat} (i : Nat) (j : Nat) : Term (bitvec n) -> Term (bitvec (i + 1 - j)) :=
  unop (extract n i j)

protected
def bvnot {n : Nat} : Term (bitvec n) -> Term (bitvec n) := unop (bvnot n)

protected
def bvneg {n : Nat} : Term (bitvec n) -> Term (bitvec n) := unop (bvneg n)

-- binops
protected
def bvand {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvand  n)
protected
def bvor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvor   n)
protected
def bvadd {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvadd  n)
protected
def bvmul {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvmul  n)
protected
def bvudiv {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvudiv n)
protected
def bvurem {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvurem n)
protected
def bvshl {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvshl  n)
protected
def bvlshr {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n) := binop (bvlshr n)
-- comparison
protected
def bvult {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvult n)


-- Functions defined by Smt as abbrevs.
protected
def bvnand {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvnand n) 
protected
def bvnor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvnor  n) 
protected
def bvxor  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvxor  n) 
protected
def bvxnor {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvxnor n) 
protected
def bvcomp {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec 1)  := binop (bvcomp n)
protected
def bvsub  {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsub  n) 
protected
def bvsdiv {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsdiv n) 
protected
def bvsrem {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsrem n) 
protected
def bvsmod {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvsmod n) 
protected
def bvashr {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term (bitvec n)  := binop (bvashr n) 

-- Defined, param by i >= 1
protected
def repeat {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (i * n)) := unop (repeat i n)

-- Defined, param by i >= 0
protected
def zeroExtend  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (n + i)) := unop (zeroExtend  i n) 
protected
def signExtend  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec (n + i)) := unop (signExtend  i n) 
protected
def rotateLeft  {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec n)       := unop (rotateLeft  i n) 
protected
def rotateRight {n : Nat} (i : Nat) : Term (bitvec n) -> Term (bitvec n)       := unop (rotateRight i n) 

protected
def bvule {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvule n) 
protected
def bvugt {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvugt n) 
protected
def bvuge {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvuge n) 
protected
def bvslt {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvslt n) 
protected
def bvsle {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsle n) 
protected
def bvsgt {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsgt n) 
protected
def bvsge {n : Nat} : Term (bitvec n) -> Term (bitvec n) -> Term bool := binop (bvsge n) 

-- Pure version, doesn't touch the symbol name
def smtLet {s t : SmtSort} (v : Symbol) (e : Term s) (body : Term s -> Term t) : Term t :=
  let v_e := mkSymbol v s;
  Raw.Term.smtLet v e (body v_e)

-- Scripts and Commands
def Script : Type := List Command

namespace Script

instance : Append Smt.Script :=
  inferInstanceAs (Append (List Command))

end Script

structure SmtState :=
  (idGen  : IdGen)
  (revScript : Script)

def SmtM := StateM SmtState

instance : Monad SmtM := inferInstanceAs (Monad (StateM SmtState))
instance : MonadStateOf SmtState SmtM := inferInstanceAs (MonadStateOf SmtState (StateM SmtState))

/- Generate a fresh symbol in the monad, if possible simply using the suggested string.  -/
def freshSymbol (suggestedStr : String) : SmtM String := do
  let (idGen', sym) ← (λ (g:IdGen) => g.genId suggestedStr) <$> SmtState.idGen <$> get
  modify (λ s => {s with idGen := idGen'})
  pure sym

def runSmtM {a : Type} (idGen : IdGen) (m : SmtM a) : (a × IdGen × Script) :=
  let r := StateT.run m { idGen := idGen, revScript := [] }
  (r.fst, (r.snd.idGen, r.snd.revScript.reverse))

theorem ConstSortToTypeFold : forall {args : List SmtSort} {res : SmtSort},
 ConstSortToType (args.foldr fsort (base res)) = funType args res := sorryAx _ -- FIXME why doesn't this work =\
-- | [], res       => rfl
-- | hd :: tl, res => 
--   have h : ConstSortToType (tl.foldr fsort (base res)) = funType tl res from ConstSortToTypeFold tl res
--   congrArg (fun r => (Term hd -> r)) h

protected
def declareFun (s : String) (args : List SmtSort) (res : SmtSort) : SmtM (funType args res) := do
  let s' ← freshSymbol s
  let ident := Raw.Ident.symbol (List.foldr fsort (base res) args) s';
  do modify (fun st => {st with revScript := (declareFun s' args res) :: st.revScript });
     pure (Eq.mp ConstSortToTypeFold ident.expandIdent)

def instArgsAux : forall (args : List SmtSort) (res : SmtSort) (body : funType args res) (acc : List (Sigma Raw.SortedVar)), 
    SmtM (List (Sigma Raw.SortedVar) × Term res) 
| [], res, body, acc    => pure (acc.reverse, body)
| hd :: tl, res, f, acc    => do   
  let s ← freshSymbol "arg"
  let arg := mkSymbol s hd
  instArgsAux tl res (f arg) (Sigma.mk hd (Raw.SortedVar.mk s) :: acc)

def instArgs (res : SmtSort) (args : List SmtSort) (body : funType args res)
    : SmtM (List (Sigma Raw.SortedVar) × Term res) :=
    instArgsAux args res body []

protected
def defineFun (s : String) (args : List SmtSort) (res : SmtSort) (body : funType args res)
  : SmtM (funType args res) := do
  let s' ← freshSymbol s
  let ident := Raw.Ident.symbol (List.foldr fsort (base res) args) s'
  let (args', body') <- instArgs res args body
  do modify (fun st => {st with revScript := (defineFun s' args' res body') :: st.revScript })
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
  if isAtomic tm then pure tm else Smt.defineFun name [] s tm





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

namespace CheckSatResult

def toString : CheckSatResult → String
  | sat => "sat"
  | unsat => "unsat"
  | unknown => "unknown"
  | unsupported => "unsupported"
  | unrecognized other => "unrecognized: " ++ other

instance : ToString CheckSatResult := ⟨toString⟩

end CheckSatResult

-- #check true
-- #check false
-- #eval toString (List.map toSExpr (runSmtM ex1))

/- Converts a command to a string terminated by a newline.-/
def Command.toLine (c:Command) : String :=
let cStr := (WellFormedSExp.SExp.toString (ToSExpr.toSExpr c));
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
