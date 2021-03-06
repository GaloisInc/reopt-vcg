
import Lean.Data.Json
import Std.Data.RBMap
universes u

open Std (RBMap)

-- Missing stuff
namespace Lean.Json

open Lean (Json FromJson ToJson)
open Lean.Json

instance rbmapToJson : ToJson (RBMap String Json Lean.strLt) :=
-- N.B., we manually have to extract the RBNode from the RBMap and have no
-- static guarantee they also used Lean.strLt =\ See
-- https://github.com/leanprover/lean4/blob/f3976fc53a883ac7606fc59357d43f4b51016ca7
-- /src/Init/Lean/Data/Json/Basic.lean#L96
-- Check back later to see if this is fixed (in reality we'll probably just break
-- at the usage of `Lean.Json.obj` when we update Lean4 and it has been changed to
-- just use the RBMap itself).
  ⟨λ rbm => Lean.Json.obj $ rbm.val⟩

section
variable  (α : Type u) [FromJson α]


-- Extract the value for the specified key of a Json object while expecting it to be of a certain
-- type (which has a HasFromJson instance).
private def parseObjValAsDescrAux (descr : String) (js:Json) (key : String) (dflt : Option α) : Except String α :=
  match js.getObjVal? key with
  | Option.some js' => match fromJson? js' with
    | Option.some a => Except.ok a
    | Option.none => 
      Except.error $ "Excepted key `"++key++"` to have a "++ descr ++" value but got `"++js'.pretty++"`."
  | Option.none => match js with
    | obj _ => match dflt with
      | Option.some a => Except.ok a
      | Option.none =>
        Except.error $ "Expected a Json object with key `"++key++"` but got `"++js.pretty++"`."
    | _ => Except.error $ "Expected a Json object but got `"++js.pretty++"`."


def parseObjValAsDescr (descr : String) (js:Json) (key : String) : Except String α :=
  @parseObjValAsDescrAux _ _ descr js key none

def parseObjValAsDescrD (descr : String) (js:Json) (key : String) (dflt : α) : Except String α :=
  @parseObjValAsDescrAux _ _ descr js key (some dflt)


end

def parseObjValAsBool := parseObjValAsDescr Bool "Bool"
def parseObjValAsBoolD := parseObjValAsDescrD Bool "Bool"
def parseObjValAsString := parseObjValAsDescr String "String"
def parseObjValAsStringD := parseObjValAsDescrD String "String"
def parseObjValAsNat := parseObjValAsDescr Nat "Nat"
def parseObjValAsNatD := parseObjValAsDescrD Nat "Nat"
def parseObjValAsInt := parseObjValAsDescr Int "Int"
def parseObjValAsIntD := parseObjValAsDescrD Int "Int"
def parseObjValAsArr := parseObjValAsDescr (Array Json) "Array"
def parseObjValAsArrD := parseObjValAsDescrD (Array Json) "Array"
def parseObjValAsArrOf (α : Type u) [FromJson α] (dscr : String) := parseObjValAsDescr (Array α) ("(Array "++dscr++")")
def parseObjValAsArrOfD (α : Type u) [FromJson α] (dscr : String) := parseObjValAsDescrD (Array α) ("(Array "++dscr++")")


private def parseObjValAsArrWithAux
{α : Type u}
(parser : Json → Except String α)
(js:Json)
(key : String)
(dflt : Option (Array α))
: Except String (Array α) :=
  match js.getObjVal? key with
  | Option.none => match dflt with
    | Option.some as => pure as
    | Option.none => Except.error $ "Expected a Json object with key `"++key++"`."
  | Option.some rawJson => match rawJson.getArr? with
    | Option.some xs => do
      let vals ← Array.mapM parser xs;
      pure vals
    | Option.none =>
      Except.error $ "Expected a Json object's `"++key
                     ++"` field to contain an array, but got `"
                     ++rawJson.pretty++"`."


-- Parse a Json object field as an array and use the given parser for the sub-elements.
def parseObjValAsArrWith {α : Type u} (parser : Json → Except String α) (js:Json) (key : String) : Except String (Array α) :=
parseObjValAsArrWithAux parser js key none

def parseObjValAsArrWithD {α : Type u} (parser : Json → Except String α) (js:Json) (key : String) (dflt : Array α) : Except String (Array α) :=
parseObjValAsArrWithAux parser js key (some dflt)





-- Equality of Json terms modulo object mapping details. It
-- gets a little gross since the RBNode interface is a little
-- messier than the RBMap interface =\
--
-- FIXME clean up when Lean.Json is updated to use RBMap instead of
-- RBNode.
partial def isEqv : Json → Json → Bool
  | null, null => true
  | bool b1, bool b2 => true
  | num n1, num n2 => n1 = n2
  | str s1, str s2 => s1 = s2
  | arr a1, arr a2 => Array.isEqv a1 a2 isEqv
  | obj kvs1, obj kvs2 =>
    match kvs1.min, kvs2.min with
    | Option.none, Option.none => true
    | Option.some ⟨k1,v1⟩, Option.some ⟨k2,v2⟩ =>
      if k1 = k2 && isEqv v1 v2 then
        let o1 := obj $ Std.RBNode.erase Lean.strLt k1 kvs1;
        let o2 := obj $ Std.RBNode.erase Lean.strLt k2 kvs2;
        isEqv o1 o2
      else 
        false
    | _,_ => false
  | _, _ => false



end Lean.Json
