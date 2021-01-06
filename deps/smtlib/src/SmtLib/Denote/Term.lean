/-
Denotations for SMT Terms (including well-formedness properties).

Copyright (c) 2020 Galois Inc. All rights reserved.
-/
import Galois.Data.Bitvec
import Galois.Data.List
import Galois.Init.Order
import SmtLib.Denote.Array
import SmtLib.Denote.Env
import SmtLib.Denote.Model
import SmtLib.Syntax


namespace Smt

namespace Raw

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
| e, x, xCS, pf, (ConstSort.base _), (Term.const _ sc), _ =>
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
  WS (e.extendMany ys) t →
  WS ((e.extend x xCS).extendMany ys) t

-- FIXME prove
axiom envNonEqSubManyWS {e : Env} {cs : ConstSort} {t : Term cs} (x : Symbol) (xCS : ConstSort) (ys : List (Sigma SortedVar)) :
  e x = none →
  (ys.find? (λ (p : Sigma SortedVar) => p.snd.var = x)).isSome ≠ true →
  WS (e.extendMany ys) t →
  WS ((e.extend x xCS).extendMany ys) t

def updMapWSBinderMany
  {e : Env}
  (x : Symbol)
  (xCS : ConstSort)
  (pf : e x = none)
  {cdom : ConstSort}
  (body : Term cdom)
  (ys : List (Sigma SortedVar))
  (ws : WS (e.extendMany ys) body)
  : WS ((e.extend x xCS).extendMany ys) body :=
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




--   ( wsDom  : forall sym s, e.find? sym = some s -> Exists (fun v => values.findEq? sym = some v))



namespace SpecConst

def semantics : forall {s : SmtSort}, SpecConst s -> s.denote.type
  | _, binary n v => bitvec.of_nat n v

end SpecConst

instance : DecidableEq Symbol := inferInstanceAs (DecidableEq String)

namespace Ident

def semantics {e : Env} (m : Model e) : forall { cs : ConstSort } (i : Ident cs), 
              Ident.WS e i -> cs.denote
| cs, Ident.symbol _ sym, ws =>
    let H : denoteDefault (e sym) = cs.denote := 
      match ws with 
      | Ident.WS.symbol pf => (congrArg denoteDefault pf);
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
          (t2 : WSTerm (updMap e x (ConstSort.base s1)) (ConstSort.base s2))
          (v1 : (ConstSort.base s1).denote)
          (v2 : (ConstSort.base s2).denote),
  Interp e m t1 v1 →
  Interp (updMap e x (ConstSort.base s1)) (m.extend x v1) t2 v2 →
  Interp e m ⟨Term.smtLet x t1.term t2.term, WS.smtLet t1.ws t2.ws⟩ v2
-- forall holds
| smtForallTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s)
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool),
  (∀ (v : s.denote.type), Interp (updMap e x.var (ConstSort.base s)) (@Model.extend _ (ConstSort.base s) m x.var v) t true) →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ true
-- forall does not hold
| smtForallFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote.type),
  Interp (updMap e x.var (ConstSort.base s)) (@Model.extend _ (ConstSort.base s) m x.var witness) t false →
  Interp e m ⟨Term.smtForall x t.term, WS.smtForall t.ws⟩ false
-- exists holds
| smtExistsTrue : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                  (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool)
                  (witness : s.denote.type),
  Interp (updMap e x.var (ConstSort.base s)) (@Model.extend _ (ConstSort.base s) m x.var witness) t true →
  Interp e m ⟨Term.smtExists x t.term, WS.smtExists t.ws⟩ true
-- exists does not hold
| smtExistsFalse : ∀ (e : Env) (m:Model e) {s : SmtSort} (x : SortedVar s) 
                     (t : WSTerm (updMap e x.var (ConstSort.base s)) ConstSort.bool),
  (∀ (v : s.denote.type), Interp (updMap e x.var (ConstSort.base s)) (@Model.extend _ (ConstSort.base s) m x.var v) t false) →
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
(bodyWS : Term.WS (e.extendMany fn.domain) fn.body)

def updMapWS {e : Env} (x : Symbol) (xCS : ConstSort) (pf : e x = none)
  {f : FunDef} (ws : WS e f) : WS (e.extend x xCS) f :=
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
  (wsPf : Term.WS (ctx.env.extendMany dom) body) : Context :=
  let f : NamedFunDef := ⟨fNm, ⟨dom, cdom, body⟩⟩;
  let env' := ctx.env.extend f.name f.funSort;
  let defines' := f::ctx.defines;
  have bodyWS : Term.WS (ctx.env.extendMany f.funDef.domain) f.funDef.body from wsPf
  have fDefWS : FunDef.WS ctx.env f.funDef from ⟨bodyWS⟩
  have fWS : NamedFunDef.WS env' f from 
    ⟨upd.atKey ctx.env f.name (some f.funSort), FunDef.updMapWS f.name f.funSort pf fDefWS⟩
  have wsDefines' : defines'.Forall (NamedFunDef.WS env') from
    List.Forall.cons fWS (ctx.wsDefines.map (@NamedFunDef.updMapWS ctx.env f.name f.funSort pf))
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
              (wsPf : Term.WS (ctx.env.extendMany dom) body),
  Interp ctx (Command.defineFun f dom cdom body) (ctx.defineFun f freshPf dom body wsPf)
-- (check-sat-assuming ...)
| checkSatAssuming : ∀ (ctx : Context) (ps : List (Term ConstSort.bool))
                     (ws : ps.Forall (Term.WS ctx.env)),
  Interp ctx (Command.checkSatAssuming ps) ctx

end Command


end Raw

end Smt
