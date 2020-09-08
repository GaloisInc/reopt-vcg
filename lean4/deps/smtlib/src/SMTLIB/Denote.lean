
import Galois.Data.List
import Galois.Data.RBMap
import SmtLib.Syntax
import SmtLib.BitVec
import Std.Data.RBMap
import Std.Data.RBTree
import Galois.Data.DRBMap


def upd.{u, v} {α : Type u} [DecidableEq α] {β: α -> Type v} (f : forall v, β v) (k : α) (v : β k) : forall v, β v :=       
  fun k' => if H : k = k' then cast (congrArg β H) v else f k'

namespace upd


universes u v
variables {α : Type u} [DecidableEq α] {β: α -> Type v}


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

-- swf dcong { δ : α -> Type } : forall (m : DRBMap α β lt) 
--           (f : forall k, m.contains k -> β k = δ k), DRBMap α δ lt



end DRBMap
end Std

namespace Smt

open Std (RBMap DRBMap)

structure Array (α β : Type) :=
(elems : List (α × β))
(dflt : β)

section
variables {α β : Type}

def Array.decEq [DecidableEq α]
                [DecidableEq β]
                (arr1 arr2 : Array α β) : Decidable (arr1 = arr2) :=
Array.casesOn arr1 $ λ elems1 dflt1 => Array.casesOn arr2 $ λ elems2 dflt2 =>
  match (decEq elems1 elems2) with
  | (isTrue e₁) =>
    match (decEq dflt1 dflt2) with
    | (isTrue e₂)  => isTrue (Eq.recOn e₁ (Eq.recOn e₂ rfl))
    | (isFalse n₂) => isFalse (fun h => Array.noConfusion h (fun e₁' e₂' => absurd e₂' n₂))
  | (isFalse n₁) => isFalse (fun h => Array.noConfusion h (fun e₁' e₂' => absurd e₁' n₁))


def Array.Less [HasLess α] [HasLess β] : Array α β → Array α β → Prop
| a1, a2 => (a1.elems, a1.dflt) < (a2.elems, a2.dflt)

instance Array.HasLess [HasLess α] [HasLess β] : HasLess (Array α β) :=
⟨@Array.Less α β _ _⟩


def Array.decLt [DecidableEq α]
                [DecidableEq β]
                [HasLess α] 
                [HasLess β]
                [forall (a1 a2 : α), Decidable (a1 < a2)]
                [forall (b1 b2 : β), Decidable (b1 < b2)]
                (arr1 arr2 : Array α β) : Decidable (arr1 < arr2) :=
Array.casesOn arr1 $ λ elems1 dflt1 => Array.casesOn arr2 $ λ elems2 dflt2 =>
  let prodLtDec : ∀ (p1 p2 : (α × β)), Decidable (p1 < p2) := prodHasDecidableLt;
  let listLtDec : ∀ (l1 l2 : List (α × β)), Decidable (l1 < l2) := List.hasDecidableLt;
  inferInstanceAs (Decidable ((elems1, dflt1) < (elems2, dflt2)))

end




@[reducible]
protected def SmtSort.denote : SmtSort → Type
| SmtSort.bool => Bool
| SmtSort.bitvec n => BitVec n
| SmtSort.array k v => Array k.denote v.denote


namespace SmtSort


private def denoteDecidableEq : forall (s : SmtSort), DecidableEq s.denote
| SmtSort.bool => Bool.DecidableEq
| SmtSort.bitvec n => BitVec.DecidableEq
| SmtSort.array k v =>
  let kHasLess := denoteDecidableEq k;
  let vHasLess := denoteDecidableEq v;
  Array.decEq


instance denote.DecidableEq : forall (s : SmtSort), DecidableEq s.denote :=
  denoteDecidableEq

inductive BoolLess : Bool → Bool → Prop
| trueLess (b : Bool) : BoolLess true b

private def boolLessImplTrue : forall {b1 b2 : Bool}, BoolLess b1 b2 → b1 = true
| true, _, _ => rfl

private def boolDecidableLt (x y : Bool) : Decidable (BoolLess x y) :=
@Bool.casesOn
  (λ b => Decidable (BoolLess b y))
  x
  (isFalse (λ (h : BoolLess false y) => Bool.noConfusion (boolLessImplTrue h)))
  (isTrue (BoolLess.trueLess y))

private def denoteHasLess : forall (s: SmtSort) , HasLess s.denote
| SmtSort.bool => {Less := BoolLess}
| SmtSort.bitvec n => {Less := @BitVec.ult n}
| SmtSort.array k v =>
  let kHasLess := denoteHasLess k;
  let vHasLess := denoteHasLess v;
  Array.HasLess


instance denote.HasLess : forall (s : SmtSort), HasLess s.denote :=
denoteHasLess


private def denoteDecidableLt : forall (s : SmtSort), forall (x y : s.denote), Decidable (x < y)
| SmtSort.bool => boolDecidableLt
| SmtSort.bitvec n => @BitVec.decidable_ult n
| SmtSort.array k v =>
  let kH := denoteDecidableLt k;
  let vH := denoteDecidableLt v;
  Array.decLt


instance denote.DecidableLt : forall (s : SmtSort), forall (x y : s.denote), Decidable (x < y) :=
denoteDecidableLt

private def denoteInhabited : forall (s : SmtSort), Inhabited s.denote
| SmtSort.bool => {default := true}
| SmtSort.bitvec n => {default := 0}
| SmtSort.array k v => {default := ⟨[], (denoteInhabited v).default⟩}

instance denote.Inhabited : forall (s : SmtSort), Inhabited s.denote :=
denoteInhabited

end SmtSort

namespace Array
section
variables {α β : Type}

protected def toList (a : Array α β) : List (α × β) :=
a.elems

protected def keys (a : Array α β) : List α :=
a.elems.map (λ e => e.fst)



protected def select [HasBeq α] (a : Array α β) (k : α) : β :=
match a.elems.lookup k with
| some v => v
| none => a.dflt


protected def store [HasLess α] [forall (x y:α), Decidable (x < y)] (a : Array α β) (k : α) (v : β) : Array α β :=
{a with elems := SortedAList.insert k v a.elems}

private def checkEntry [HasBeq α] (a : Array α β) (k : α) (p : β → Bool) : Bool :=
match a.elems.lookup k with
| some v => p v
| none => false

end

private def bvEqRangeAux {β n} [HasBeq β] (a1 a2 : Array (BitVec n) β) (low : BitVec n) : Nat → Bool
| Nat.zero => a1.select 0 == a2.select 0
| Nat.succ i =>
  let idx := low + (BitVec.ofNat n i) + 1;
  a1.select idx == a2.select idx && bvEqRangeAux i

def bvEqRange {β n} [HasBeq β] (a1 a2 : Array (BitVec n) β) (low high : BitVec n) : Bool :=
if BitVec.ult high low then true
else
  let rangeSize := high - low;
  bvEqRangeAux a1 a2 low rangeSize.toNat


def eqRange {β} [HasBeq β] :
  forall (s : RangeSort),
  Array s.sort.denote β →
  Array s.sort.denote β →
  s.sort.denote →
  s.sort.denote → Bool
| RangeSort.bitvec n, a1, a2, low, high => bvEqRange a1 a2 low high

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
| ConstSort.base s => s.denote
| ConstSort.fsort a b => a.denote → b.denote

end ConstSort

namespace VarArgs

private def varArgsPred (α : Type) : Nat → Type
| 0 => Bool
| Nat.succ n => α → varArgsPred n


private def distinctList {α : Type} [DecidableEq α] : List α → Bool
| [] => true
| a::as => !(as.contains a) && distinctList as


def distinct (s : SmtSort) : forall (n : Nat), List s.denote → (nary s SmtSort.bool n).denote
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

| _, BuiltinIdent.select _ _           => Array.select
| _, BuiltinIdent.store  _ _           => Array.store
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
           let pf' : (updMap e k cs) sym = e sym := upd.updAtOther e (some cs) H;
           cast (congrArg denoteDefault pf'.symm)
                (m.values sym : denoteDefault (e sym))
  }

end Model

namespace SpecConst

def semantics : forall {s : SmtSort}, SpecConst s -> s.denote
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
  (∀ (v : s.denote), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t true) →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ true
-- forall does not hold
| smtForallFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t false →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ false
-- exists holds
| smtExistsTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote),
  Interp (upd e x.var (ConstSort.base s)) (m.extend x.var witness) t true →
  Interp e m ⟨Term.smtExists x t.term, WS.smtExists t.ws⟩ true
-- exists does not hold
| smtExistsFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                     (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool),
  (∀ (v : s.denote), Interp (upd e x.var (ConstSort.base s)) (m.extend x.var v) t false) →
  Interp e m ⟨Term.smtExists x t.term, WS.smtExists t.ws⟩ false


end Term


structure FunDef :=
(domain : List (Sigma SortedVar))
(codomain : SmtSort)
(body : Term (ConstSort.base codomain))


namespace FunDef

def funSort (f : FunDef) : ConstSort :=
ConstSort.funSort f.domain f.codomain

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
ConstSort.funSort f.funDef.domain f.funDef.codomain

structure WS (e : Env) (fn : NamedFunDef) : Prop :=
(funInEnv : e fn.name = some fn.funSort)
(funDefWS : FunDef.WS e fn.funDef)

def updMapWS {e : Env} (x : Symbol) (xCS : ConstSort) (pf : e x = none)
  {f : NamedFunDef} (ws : WS e f) : WS (updMap e x xCS) f :=
have h : x ≠ f.name from updMap.noneSomeNEqKey e x f.name pf f.funInEnv;
have inEnv : (updMap e x xCS) f.name = some f.funSort
  from upd.atOtherKey e (some f.funSort) h;
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
let env' := updMap ctx.env f fSort;
{ctx with
  env := env',
  wsAsserts := ctx.wsAsserts.map (Term.updMapWS f fSort)
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
let fWS : NamedFunDef.WS env' f := ⟨rfl, FunDef.updMapWS fNm f.funSort pf wsPf⟩;
let wsDefines' : defines'.Forall (NamedFunDef.WS env') :=
  fWS::(ctx.wsDefines.map (NamedFunDef.updMapWS env f.name f.funSort pf));
{ctx with
  env := env',
  wsAsserts := ctx.wsAsserts.map (Term.updMapWS f.name f.funSort),
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
