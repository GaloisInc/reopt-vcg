/-
Defines the model for interpreting SMT terms (i.e.,
the mapping from free variables to values).

Copyright (c) 2020 Galois Inc. All rights reserved.
-/

import SmtLib.Syntax
import SmtLib.Denote.BuiltinId
import SmtLib.Denote.Env


namespace Smt

namespace Raw

def denoteDefault (cs : Option ConstSort) : Type := 
   match cs with 
   | none   => Unit
   | some v => ConstSort.denote v

structure Model ( e : Env ) :=
  ( values : forall (sym : Symbol), denoteDefault (e sym) )


namespace Model

def extend {e : Env} {cs : ConstSort} (m : Model e) (k : Symbol) (v : cs.denote) 
  : Model (e.extend k cs) :=
   let pf : forall {sym} (pf : k = sym), denoteDefault ((e.extend k cs) sym) = cs.denote :=
     fun _ pf => congrArg denoteDefault (difPos pf);
  { values := fun sym => 
           if H : k = sym then cast (pf H).symm v 
           else 
           let pf' : (e.extend k cs) sym = e sym := upd.atOtherKey e (some cs) H;
           cast (congrArg denoteDefault pf'.symm)
                (m.values sym : denoteDefault (e sym))
  }

end Model

end Raw

end Smt
