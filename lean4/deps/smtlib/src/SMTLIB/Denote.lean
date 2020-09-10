
import Galois.Init.Order
import Galois.Data.DRBMap
import Galois.Data.List
import Galois.Data.RBMap
import SmtLib.Array
import SmtLib.Syntax
import SmtLib.BitVec
import Std.Data.RBMap
import Std.Data.RBTree



def upd.{u, v} {α : Type u} [DecidableEq α] {β: α -> Type v} (f : forall v, β v) (k : α) (v : β k) : forall v, β v :=       
  fun k' => if H : k = k' then cast (congrArg β H) v else f k'

namespace upd


universes u v
variables {α : Type u} [DecidableEq α] {β: α -> Type v}

theorem atKey (f : forall v, β v) (k : α)  (v : β k) : (upd f k v) k = v :=
  difPos rfl


theorem atOtherKey {k k'} (f : forall v, β v) (v : β k) (pf : k ≠ k') : (upd f k v) k' = f k' :=
  difNeg pf       


end upd


def updMap {α β : Type} [DecidableEq α] (f : α -> Option β) (k : α) (v : β) :  α -> Option β :=
  upd f k (some v)

namespace updMap

def noneSomeNEqKey {α β : Type} [DecidableEq α] (f : α -> Option β) (x y : α) (xPf : f x = none) {v : β} (yPf : f y = some v) : x ≠ y :=
λ h =>
  let yPf' : f y = none := h ▸ xPf;
  let absurd : none = some v := Eq.trans yPf'.symm yPf;
  Option.noConfusion absurd

end updMap

namespace Std

namespace DRBMap

universes u v

variables {α : Type u} {β : α → Type v} {lt : α → α → Bool}

def keys : DRBMap α β lt → List α 
| ⟨t, _⟩ => t.revFold (fun ps k v => k::ps) []


end DRBMap
end Std

namespace Smt

open Std (RBMap DRBMap)

namespace Bool

inductive Less : Bool → Bool → Prop
| lt : Less true false

private def lessLeftTrue : forall {b1 b2 : Bool}, Less b1 b2 → b1 = true
| true, _, _ => rfl

private def lessRightFalse : forall {b1 b2 : Bool}, Less b1 b2 → b2 = false
| _, false, _ => rfl


private def boolDecidableLt (x y : Bool) : Decidable (Less x y) :=
@Bool.casesOn
  (λ b => Decidable (Less b y))
  x
  (isFalse (λ (h : Less false y) => Bool.noConfusion (lessLeftTrue h)))
  (@Bool.casesOn
    (λ b => Decidable (Less true b))
    y
    (isTrue Less.lt)
    (isFalse (λ (h : Less true true) => Bool.noConfusion (lessRightFalse h))))


instance : HasLess Bool := ⟨Less⟩
instance : DecidableLess Bool := boolDecidableLt

axiom Less.transitivity :∀ (x y z : Bool), x < y → y < z → x < z
axiom Less.asymmetry : ∀ (x y : Bool), x < y → ¬(y < x)
axiom Less.totality : ∀ (x y : Bool), x < y ∨ x = y ∨ y < x

instance : HasLessOrder Bool :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance : DecidableLessOrder Bool :=
{ltDec := Bool.DecidableLess,
 eqDec := Bool.DecidableEq}

end Bool


namespace BitVec

def Less {n : Nat} : BitVec n → BitVec n → Prop := BitVec.ult

instance (n:Nat) : HasLess (BitVec n) := ⟨BitVec.Less⟩
instance (n:Nat) : DecidableLess (BitVec n) := @BitVec.decidable_ult n 

axiom Less.transitivity {n} : ∀ (x y z : BitVec n), x < y → y < z → x < z
axiom Less.asymmetry {n} : ∀ (x y : BitVec n), x < y → ¬(y < x)
axiom Less.totality {n} : ∀ (x y : BitVec n), x < y ∨ x = y ∨ y < x

instance {n} : HasLessOrder (BitVec n) :=
{transitive := Less.transitivity,
 asymmetric := Less.asymmetry,
 total := Less.totality}


instance {n} : DecidableLessOrder (BitVec n) :=
{ltDec := @BitVec.DecidableLess n,
 eqDec := @BitVec.DecidableEq n}

end BitVec


structure OrderedType :=
(type : Type)
(order : DecidableLessOrder type)


@[reducible]
protected def SmtSort.denote : SmtSort → OrderedType
| SmtSort.bool => ⟨Bool, Bool.DecidableLessOrder⟩
| SmtSort.bitvec n => ⟨BitVec n, BitVec.DecidableLessOrder⟩
| SmtSort.array k v =>
  let k' := k.denote;
  let kOrd := k'.order;
  let v' := v.denote;
  let vOrd := v'.order;
  ⟨Array k'.type v'.type, Array.DecidableLessOrder⟩


instance SmtSort.denote.HasLess : ∀ (s:SmtSort), HasLess s.denote.type
| s => ⟨s.denote.order.Less⟩


instance SmtSort.denote.DecidableLess : ∀ (s:SmtSort), DecidableLess s.denote.type
| s => s.denote.order.ltDec


instance SmtSort.denote.DecidableEq : ∀ (s:SmtSort), DecidableEq s.denote.type
| s => s.denote.order.eqDec


instance SmtSort.denote.DecidableLessOrder : ∀ (s:SmtSort), DecidableLessOrder s.denote.type
| s => s.denote.order



namespace Array
section
variables {α β : Type} [DecidableLessOrder α] [DecidableLessOrder β]


private def bvEqRangeAux {n} (a1 a2 : Array (BitVec n) β) (low : BitVec n) : Nat → Bool
| Nat.zero => a1.select 0 == a2.select 0
| Nat.succ i =>
  let idx := low + (BitVec.ofNat n i) + 1;
  a1.select idx == a2.select idx && bvEqRangeAux i

end

section
variables {β : Type} [DecidableLessOrder β]


def bvEqRange {n} (a1 a2 : Array (BitVec n) β) (low high : BitVec n) : Bool :=
if high < low then true
else
  let rangeSize := high - low;
  bvEqRangeAux a1 a2 low rangeSize.toNat


def eqRange :
  forall (k : RangeSort),
  Array k.sort.denote.type β →
  Array k.sort.denote.type β →
  k.sort.denote.type →
  k.sort.denote.type → Bool
| RangeSort.bitvec n, a1, a2, low, high => bvEqRange a1 a2 low high


end

end Array



namespace Raw

def Env := Symbol -> Option ConstSort

namespace Env

def empty : Env := λ _ => none

end Env

def updEnvMany (e : Env) (entries : List (Sigma SortedVar)) : Env :=
  entries.foldr (λ p e' => updMap e' p.snd.var (ConstSort.base p.fst)) e


--------------------------------------------------------------------------------
-- Well sorted terms
--
-- Because we have typed terms, well-sortedness boils down to the
-- variables having the claimed sort.

namespace Ident

inductive WS : forall {cs : ConstSort}, Env → Ident cs → Prop
| symbol : ∀ {e : Env} {cs : ConstSort} {x : Symbol}, e x = some cs → WS e (Ident.symbol cs x)
| builtin : ∀ (e : Env) {cs : ConstSort} (b : BuiltinIdent cs), WS e (Ident.builtin b)

def updMapWS {e : Env} (x : Symbol) (xPf : e x = none) (xCS : ConstSort) :
  ∀ {cs : ConstSort} (y : Ident cs) (ws : WS e y), WS (updMap e x xCS) y
| _, (Ident.symbol cs y), (WS.symbol (yPf : e y = some cs)) =>
  let h : x ≠ y := updMap.noneSomeNEqKey e x y xPf yPf;
  let yPf' : (updMap e x xCS) y = e y := upd.atOtherKey e (some xCS) h;
  let yPf'' : (updMap e x xCS) y = some cs := Eq.trans yPf' yPf;
  WS.symbol yPf''
| _, (Ident.builtin b), _ => WS.builtin (updMap e x xCS) b

end Ident

namespace Term

-- Well sorted term definition.
inductive WS : forall {cs : ConstSort}, Env → Term cs → Prop
| const : ∀ (e : Env) {s : SmtSort} (sc : SpecConst s), WS e (Term.const s sc)
| ident : ∀ {e : Env} {cs : ConstSort} {x : Ident cs}, Ident.WS e x → WS e (Term.ident x)
| app   : ∀ {e : Env} {s : SmtSort} {cs : ConstSort}
         {t1 : Term (ConstSort.fsort s cs)}
         {t2 : Term (ConstSort.base s)},
  WS e t1 →
  WS e t2 →
  WS e (Term.app t1 t2)
| smtLet : ∀ {e : Env} {s1 s2 : SmtSort} {x : Symbol}
           {t1 : Term (ConstSort.base s1)}
           {t2 : Term (ConstSort.base s2)},
  WS e t1 →
  WS (updMap e x (ConstSort.base s1)) t2 →
  WS e (Term.smtLet x t1 t2)
| smtForall : ∀ {e : Env} {s : SmtSort} {x : SortedVar s} {t : Term ConstSort.bool},
  WS (updMap e x.var (ConstSort.base s)) t →
  WS e (Term.smtForall x t)
| smtExists : ∀ {e : Env} {s : SmtSort} {x : SortedVar s} {t : Term ConstSort.bool},
  WS (updMap e x.var (ConstSort.base s)) t →
  WS e (Term.smtExists x t)


-- FIXME prove
axiom envShadowWS {e : Env} {cs : ConstSort} {t : Term cs} (x : Symbol) (xCS xCS' : ConstSort) :
  WS (updMap e x xCS') t →
  WS (updMap (updMap e x xCS) x xCS') t

-- FIXME prove
axiom envNonEqSubWS {e : Env} {cs : ConstSort} {t : Term cs} (x y : Symbol) (xCS yCS : ConstSort) :
  e x = none →
  x ≠ y →
  WS (updMap e y yCS) t →
  WS (updMap (updMap e x xCS) y yCS) t

def updMapWSBinder
  {e : Env}
  (x : Symbol)
  (xCS : ConstSort)
  (pf : e x = none)
  {y : Symbol}
  {cs yCS : ConstSort}
  (t : Term cs)
  (ws : WS (updMap e y yCS) t)
  : WS (updMap (updMap e x xCS) y yCS) t :=
if h : x = y
then
  have hWS : WS (updMap (updMap e y xCS) y yCS) t from envShadowWS y xCS yCS ws;
  h.symm ▸ hWS
else
  envNonEqSubWS x y xCS yCS pf h ws


theorem updMapWS : ∀ {e : Env} (x : Symbol) (xCS : ConstSort) (pf : e x = none)
                   {cs : ConstSort} {t : Term cs} (ws : WS e t), WS (updMap e x xCS) t
-- const
| e, x, xCS, _, _, (Term.const _ sc), _ =>
  WS.const (updMap e x xCS) sc
-- ident
| _, x, xCS, pf, _, (Term.ident y), (Term.WS.ident yWS) =>
  WS.ident (Ident.updMapWS x pf xCS y yWS)
-- app
| _, x, xCS, pf, _, (Term.app t1 t2), (Term.WS.app ws1 ws2) =>
  WS.app (updMapWS x xCS pf ws1) (updMapWS x xCS pf ws2)
-- let
| e, x, xCS, pf, cs@(ConstSort.base _), (Term.smtLet y t1 t2), (WS.smtLet ws1 (ws2 : WS (updMap e y _) t2)) =>
  let ws1' : WS (updMap e x xCS) t1 := updMapWS x xCS pf ws1;
  let ws2' : WS (updMap (updMap e x xCS) y _) t2 := updMapWSBinder x xCS pf t2 ws2;
  WS.smtLet ws1' ws2'
-- forall
| e, x, xCS, pf, (ConstSort.base SmtSort.bool), (@Term.smtForall s ⟨y⟩ t), (WS.smtForall ws) =>
  let yCS := ConstSort.base s;
  let ws' : WS (updMap (updMap e x xCS) y yCS) t := updMapWSBinder x xCS pf t ws;
  WS.smtForall ws'
-- -- exists
| e, x, xCS, pf, (ConstSort.base SmtSort.bool), (@Term.smtExists s ⟨y⟩ t), (WS.smtExists ws) =>
  let yCS := ConstSort.base s;
  let ws' : WS (updMap (updMap e x xCS) y yCS) t := updMapWSBinder x xCS pf t ws;
  WS.smtExists ws'

-- FIXME prove
axiom envShadowManyWS {e : Env} {cs : ConstSort} {t : Term cs} (x : Symbol) (xCS : ConstSort) (ys : List (Sigma SortedVar)) :
  (ys.find? (λ (p : Sigma SortedVar) => p.snd.var = x)).isSome = true →
  WS (updEnvMany e ys) t →
  WS (updEnvMany (updMap e x xCS) ys) t

-- FIXME prove
axiom envNonEqSubManyWS {e : Env} {cs : ConstSort} {t : Term cs} (x : Symbol) (xCS : ConstSort) (ys : List (Sigma SortedVar)) :
  e x = none →
  (ys.find? (λ (p : Sigma SortedVar) => p.snd.var = x)).isSome ≠ true →
  WS (updEnvMany e ys) t →
  WS (updEnvMany (updMap e x xCS) ys) t

def updMapWSBinderMany
  {e : Env}
  (x : Symbol)
  (xCS : ConstSort)
  (pf : e x = none)
  {cdom : ConstSort}
  (body : Term cdom)
  (ys : List (Sigma SortedVar))
  (ws : WS (updEnvMany e ys) body)
  : WS (updEnvMany (updMap e x xCS) ys) body :=
if h : (ys.find? (λ (p : Sigma SortedVar) => p.snd.var = x)).isSome = true
then envShadowManyWS x xCS ys h ws
else envNonEqSubManyWS x xCS ys pf h ws


end Term

structure WSTerm (env : Env) (cs : ConstSort) : Type :=
(term : Term cs)
(ws   : Term.WS env term)

namespace WSTerm

-- FIXME does it matter that this doesn't relate the underlying term in the output to the one in the input?
-- def updMapWS {e : Env} {cs : ConstSort} (t : WSTerm e cs) (x : Symbol) (xCS : ConstSort) (pf : e x = none) : WSTerm (updMap e x xCS) cs :=
-- ⟨t.term, Term.updMapWS x xCS pf t.term t.ws⟩



end WSTerm

namespace ConstSort

@[reducible]
protected def denote : ConstSort → Type
| ConstSort.base s => s.denote.type
| ConstSort.fsort a b => a.denote.type → (denote b)

end ConstSort

namespace VarArgs

private def varArgsPred (α : Type) : Nat → Type
| 0 => Bool
| Nat.succ n => α → varArgsPred n


private def distinctList {α : Type} [DecidableEq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote.type → (nary s SmtSort.bool n).denote
| 0, args => distinctList args
| Nat.succ n, args => λ a => (distinct n) (a::args)

end VarArgs


private def mkDistinct (s : SmtSort) (n : Nat) : (nary s SmtSort.bool n).denote :=
VarArgs.distinct s n []


@[reducible]
protected def BuiltinIdent.denote : forall cs, BuiltinIdent cs → cs.denote
-- * Core theory
| _, BuiltinIdent.true => true
| _, BuiltinIdent.false => false
| _, BuiltinIdent.not => not
| _, BuiltinIdent.impl => λ p q => !p || q
| _, BuiltinIdent.and => and
| _, BuiltinIdent.or => or
| _, BuiltinIdent.xor => xor
| _, BuiltinIdent.eq s => λ x y => x = y
| _, BuiltinIdent.smtIte s => λ t x y => if t then x else y
| _, BuiltinIdent.distinct s n => mkDistinct s n

| _, BuiltinIdent.select k v           => Array.select
| _, BuiltinIdent.store  k v           => Array.store
| _, BuiltinIdent.eqrange k _          => Array.eqRange k

-- -- * BitVecs
-- -- hex/binary literals
| _, BuiltinIdent.concat _ _           => BitVec.append
| _, BuiltinIdent.extract n i j        => BitVec.extract i j
-- -- unops
| _, BuiltinIdent.bvnot   _            => BitVec.not
| _, BuiltinIdent.bvneg   _            => BitVec.neg
-- -- binops                   
| _, BuiltinIdent.bvand   _            => BitVec.and
| _, BuiltinIdent.bvor    _            => BitVec.or
| _, BuiltinIdent.bvadd   _            => BitVec.add
| _, BuiltinIdent.bvmul   _            => BitVec.mul
| _, BuiltinIdent.bvudiv  _            => BitVec.udiv
| _, BuiltinIdent.bvurem  _            => BitVec.urem
| _, BuiltinIdent.bvshl   _            => λ b i => BitVec.shl b i.toNat
| _, BuiltinIdent.bvlshr  _            => λ b i => BitVec.ushr b i.toNat
-- -- comparison               
| _, BuiltinIdent.bvult   _            => λ b1 b2 => decide (BitVec.ult b1 b2)

| _, BuiltinIdent.bvnand  _            => λ b1 b2 => BitVec.not (BitVec.and b1 b2)
| _, BuiltinIdent.bvnor   _            => λ b1 b2 => BitVec.not (BitVec.or b1 b2)
| _, BuiltinIdent.bvxor   _            => BitVec.xor
| _, BuiltinIdent.bvxnor  _            => λ b1 b2 => BitVec.not (BitVec.xor b1 b2)
| _, BuiltinIdent.bvcomp  _            => λ b1 b2 => if b1 = b2 then 1 else 0
| _, BuiltinIdent.bvsub   _            => BitVec.sub
| _, BuiltinIdent.bvsdiv  _            => BitVec.sdiv
| _, BuiltinIdent.bvsrem  _            => BitVec.srem
| _, BuiltinIdent.bvsmod  _            => BitVec.smod
| _, BuiltinIdent.bvashr  _            => λ b i => BitVec.sshr b i.toNat

| _, BuiltinIdent.repeat i _           => λ b => BitVec.repeat b i

| _, BuiltinIdent.zeroExtend  i n     => λ b => b.uresize (n + i)
| _, BuiltinIdent.signExtend  i n     => λ b => b.sresize (n + i)
| _, BuiltinIdent.rotateLeft  i _     => BitVec.rotateLeft i
| _, BuiltinIdent.rotateRight i _     => BitVec.rotateRight i

| _, BuiltinIdent.bvule _              => λ x y => decide (BitVec.ule x y)
| _, BuiltinIdent.bvugt _              => λ x y => decide (BitVec.ugt x y)
| _, BuiltinIdent.bvuge _              => λ x y => decide (BitVec.uge x y)
| _, BuiltinIdent.bvslt _              => λ x y => decide (BitVec.slt x y)
| _, BuiltinIdent.bvsle _              => λ x y => decide (BitVec.sle x y)
| _, BuiltinIdent.bvsgt _              => λ x y => decide (BitVec.sgt x y)
| _, BuiltinIdent.bvsge _              => λ x y => decide (BitVec.sge x y)


def denoteDefault (cs : Option ConstSort) : Type := 
   match cs with 
   | none   => Unit
   | some v => ConstSort.denote v

structure Model ( e : Env ) :=
  ( values : forall (sym : Symbol), denoteDefault (e sym) )
--   ( wsDom  : forall sym s, e.find? sym = some s -> Exists (fun v => values.findEq? sym = some v))


namespace Model

def extend {e : Env} {cs : ConstSort} (m : Model e) (k : Symbol) (v : cs.denote) 
  : Model (updMap e k cs) :=
   let pf : forall {sym} (pf : k = sym), denoteDefault ((updMap e k cs) sym) = cs.denote :=
     fun _ pf => congrArg denoteDefault (difPos pf);   
  { values := fun sym => 
           if H : k = sym then cast (pf H).symm v 
           else 
           let pf' : (updMap e k cs) sym = e sym := upd.atOtherKey e (some cs) H;
           cast (congrArg denoteDefault pf'.symm)
                (m.values sym : denoteDefault (e sym))
  }

end Model

namespace SpecConst

def semantics : forall {s : SmtSort}, SpecConst s -> s.denote.type
  | _, binary n v => BitVec.ofNat n v

end SpecConst

instance : DecidableEq Symbol := inferInstanceAs (DecidableEq String)

namespace Ident

def semantics {e : Env} (m : Model e) : forall { cs : ConstSort } (i : Ident cs), 
              Ident.WS e i -> cs.denote
| _, symbol cs sym, ws =>
    let H : denoteDefault (e sym) = cs.denote := 
      match ws with | (Ident.WS.symbol pf) => (congrArg denoteDefault pf);
    let v : denoteDefault (e sym) := m.values sym;
    cast H v

| _, builtin i, _    => BuiltinIdent.denote _ i

end Ident


namespace Term

inductive Interp : forall (e:Env) (m:Model e) {cs:ConstSort}, WSTerm e cs → cs.denote → Prop
-- const
| const : ∀ (e:Env) (m:Model e) {s : SmtSort} (sc : SpecConst s),
  Interp e m ⟨Term.const s sc, WS.const e sc⟩ sc.semantics
-- ident
| ident : ∀ (e:Env) (m:Model e) {cs : ConstSort} (x : Ident cs) (xWS : Ident.WS e x),
  Interp e m ⟨Term.ident x, WS.ident xWS⟩ (Ident.semantics m x xWS)
-- app
| app  :  ∀ (e:Env) (m:Model e) {s : SmtSort} {cs : ConstSort} 
  (t1 : WSTerm e (ConstSort.fsort s cs))
  (t2 : WSTerm e (ConstSort.base s))
  (f : (ConstSort.fsort s cs).denote)
  (x : (ConstSort.base s).denote),
  Interp e m t1 f →
  Interp e m t2 x →
  Interp e m ⟨Term.app t1.term t2.term, WS.app t1.ws t2.ws⟩ (f x)
-- let
| smtLet : ∀ (e:Env) (m:Model e) {s1 s2 : SmtSort} (x : Symbol)
          (t1 : WSTerm e (ConstSort.base s1))
          (t2 : WSTerm (upd e x (ConstSort.base s1)) (ConstSort.base s2))
          (v1 : (ConstSort.base s1).denote)
          (v2 : (ConstSort.base s2).denote),
  Interp e m t1 v1 →
  Interp (upd e x (ConstSort.base s1)) (m.extend x v1) t2 v2 →
  Interp e m ⟨Term.smtLet x t1.term t2.term, WS.smtLet t1.ws t2.ws⟩ v2
-- forall holds
| smtForallTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s)
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool),
  (∀ (v : s.denote.type), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t true) →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ true
-- forall does not hold
| smtForallFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote.type),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t false →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ false
-- exists holds
| smtExistsTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote.type),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t true →
  Interp e m ⟨Term.smtExists x t.term, WS.smtExists t.ws⟩ true
-- exists does not hold
| smtExistsFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                     (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool),
  (∀ (v : s.denote.type), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t false) →
  Interp e m ⟨Term.smtExists x t.term, WS.smtExists t.ws⟩ false


end Term


structure FunDef :=
(domain : List (Sigma SortedVar))
(codomain : SmtSort)
(body : Term (ConstSort.base codomain))


namespace FunDef

def funSort (f : FunDef) : ConstSort :=
ConstSort.funSort (f.domain.map (λ sv => sv.fst)) f.codomain

structure WS (e : Env) (fn : FunDef) : Prop :=
(bodyWS : Term.WS (updEnvMany e fn.domain) fn.body)

def updMapWS {e : Env} (x : Symbol) (xCS : ConstSort) (pf : e x = none)
  {f : FunDef} (ws : WS e f) : WS (updMap e x xCS) f :=
⟨Term.updMapWSBinderMany x xCS pf f.body f.domain ws.bodyWS⟩

end FunDef

structure NamedFunDef :=
(name : Symbol)
(funDef : FunDef)

namespace NamedFunDef

def funSort (f : NamedFunDef) : ConstSort :=
ConstSort.funSort (f.funDef.domain.map (λ sv => sv.fst)) f.funDef.codomain

structure WS (e : Env) (fn : NamedFunDef) : Prop :=
(funInEnv : e fn.name = some fn.funSort)
(funDefWS : FunDef.WS e fn.funDef)

def updMapWS {e : Env} (x : Symbol) (xCS : ConstSort) (pf : e x = none)
  {f : NamedFunDef} (ws : WS e f) : WS (updMap e x xCS) f :=
have h : x ≠ f.name from updMap.noneSomeNEqKey e x f.name pf ws.funInEnv;
-- have inEnv : (updMap e x xCS) f.name = e f.name
--   from upd.atOtherKey e (some f.funSort) h;
have inEnv : (updMap e x xCS) f.name = some f.funSort
  from Eq.trans (upd.atOtherKey e (some xCS) h) ws.funInEnv;
have defWS : FunDef.WS (updMap e x xCS) f.funDef
  from FunDef.updMapWS x xCS pf ws.funDefWS;
⟨inEnv, defWS⟩


end NamedFunDef

-- An SMT context defined by the top-level commands in a script.
structure Context :=
-- | The envirnoment of in-scope names and their sort.
(env : Env)
-- | Terms asserted to be true.
(asserts : List (Term ConstSort.bool))
-- | Assertions are well-sorted.
(wsAsserts : asserts.Forall (Term.WS env))
-- | Names defined via the `define-fun` command.
(defines : List NamedFunDef)
-- | Defined functions are well-sorted.
(wsDefines : defines.Forall (NamedFunDef.WS env))

namespace Context

def empty : Context :=
{ env := Env.empty,
  asserts := [],
  wsAsserts := List.Forall.nil,
  defines := [],
  wsDefines := List.Forall.nil
}

def assert (ctx : Context) (p : WSTerm ctx.env ConstSort.bool) : Context :=
{ctx with asserts := p.term :: ctx.asserts,
          wsAsserts := List.Forall.cons p.ws ctx.wsAsserts
}

def declareFun (ctx : Context) (f : Symbol) (pf : ctx.env f = none) (dom : List SmtSort) (cdom : SmtSort) : Context :=
let fSort := ConstSort.funSort dom cdom;
{ctx with
  env := updMap ctx.env f fSort,
  wsAsserts := ctx.wsAsserts.map (@Term.updMapWS ctx.env f fSort pf ConstSort.bool),
  wsDefines := ctx.wsDefines.map (@NamedFunDef.updMapWS ctx.env f fSort pf)
}

def defineFun
  (ctx : Context)
  (fNm : Symbol)
  (pf : ctx.env fNm = none)
  (dom : List (Sigma SortedVar))
  {cdom : SmtSort}
  (body : Term (ConstSort.base cdom))
  (wsPf : Term.WS (updEnvMany ctx.env dom) body) : Context :=
let f : NamedFunDef := ⟨fNm, ⟨dom, cdom, body⟩⟩;
let env' := updMap ctx.env f.name f.funSort;
let defines' := f::ctx.defines;
let fWS : NamedFunDef.WS env' f := ⟨upd.atKey ctx.env fNm (some f.funSort), FunDef.updMapWS fNm f.funSort pf ⟨wsPf⟩⟩;
let wsDefines' : defines'.Forall (NamedFunDef.WS env') :=
  List.Forall.cons fWS (ctx.wsDefines.map (@NamedFunDef.updMapWS ctx.env f.name f.funSort pf));
{ctx with
  env := env',
  wsAsserts := ctx.wsAsserts.map (@Term.updMapWS ctx.env f.name f.funSort pf ConstSort.bool),
  defines := defines',
  wsDefines := wsDefines'
}

end Context

namespace Command

-- Describes how commands update the SMT context.
inductive Interp : Context → Command → Context → Prop
-- (assert ...)
| assert : ∀ (ctx : Context) (p : WSTerm ctx.env ConstSort.bool),
  Interp ctx (Command.assert p.term) (ctx.assert p)
-- (set-logic ...)
| setLogic : ∀ (ctx : Context) (l : Logic),
  Interp ctx (Command.setLogic l) ctx
-- (set-option ...)
| setOption : ∀ (ctx : Context) (o : Opt),
  Interp ctx (Command.setOption o) ctx
-- // comment
| comment : ∀ (ctx : Context) (msg : String),
  Interp ctx (Command.comment msg) ctx
-- (declare-fun ...)
| declareFun : ∀ (ctx : Context) (f : Symbol) (dom : List SmtSort) (cdom : SmtSort)
               (pf : ctx.env f = none),
  Interp ctx (Command.declareFun f dom cdom) (ctx.declareFun f pf dom cdom)
-- (define-fun ...)
| defineFun : ∀ (ctx : Context) (f : Symbol) (freshPf : ctx.env f = none)
              (dom : List (Sigma SortedVar)) {cdom : SmtSort}
              (body : Term (ConstSort.base cdom))
              (wsPf : Term.WS (updEnvMany ctx.env dom) body),
  Interp ctx (Command.defineFun f dom cdom body) (ctx.defineFun f freshPf dom body wsPf)
-- (check-sat-assuming ...)
| checkSatAssuming : ∀ (ctx : Context) (ps : List (Term ConstSort.bool))
                     (ws : ps.Forall (Term.WS ctx.env)),
  Interp ctx (Command.checkSatAssuming ps) ctx

end Command


end Raw

end Smt
