
import Init.Lean.Data.Json
import Init.Data.RBMap
universes u

-- Missing stuff
namespace Lean.Json

open Lean (Json HasFromJson HasToJson)
open Lean.Json

instance rbmapToJson : HasToJson (RBMap String Json Lean.strLt) :=
-- N.B., we manually have to extract the RBNode from the RBMap and have no
-- static guarantee they also used Lean.strLt =\ See
-- https://github.com/leanprover/lean4/blob/f3976fc53a883ac7606fc59357d43f4b51016ca7
-- /src/Init/Lean/Data/Json/Basic.lean#L96
-- Check back later to see if this is fixed (in reality we'll probably just break
-- at the usage of `Lean.Json.obj` when we update Lean4 and it has been changed to
-- just use the RBMap itself).
⟨λ rbm => Lean.Json.obj $ rbm.val⟩

section
variables  (α : Type u) [HasFromJson α]

-- Extract the value for the specified key of a Json object while expecting it to be of a certain
-- type (which has a HasFromJson instance).
def parseObjValAsDescr (descr : String) (js:Json) (key : String) : Except String α :=
match js.getObjVal? key with
| Option.some js' => 
  match fromJson? js' with
  | Option.some a => Except.ok a
  | Option.none => 
    Except.error $ "Excepted key `"++key++"` to have a "++ descr ++" value but got `"++js'.pretty++"`."
| Option.none => Except.error $ "Expected a Json object with key `"++key++"` but got `"++js.pretty++"`."

-- Like parseObjValAsDescr but with a default value if the field is missing.
def parseObjValAsDescrD (descr : String) (js:Json) (key : String) (dflt : α) : Except String α :=
match js.getObjVal? key with
| Option.some js' => 
  match fromJson? js' with
  | Option.some a => Except.ok a
  | Option.none => 
    Except.error $ "Excepted key `"++key++"` to have a "++ descr ++" value but got `"++js'.pretty++"`."
| Option.none => 
  match js with
  | obj _ => Except.ok dflt
  | _ => Except.error $ "Expected a Json object but got `"++js.pretty++"`."


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
def parseObjValAsArrOf (α : Type u) [HasFromJson α] (dscr : String) := parseObjValAsDescr (Array α) ("(Array "++dscr++")")
def parseObjValAsArrOfD (α : Type u) [HasFromJson α] (dscr : String) := parseObjValAsDescrD (Array α) ("(Array "++dscr++")")

-- Parse a Json object field as an array and use the given parser for the sub-elements.
def parseObjValAsArrWith {α : Type u} [HasFromJson α] (parser : Json → Except String α) (js:Json) (key : String) : Except String (Array α) :=
match parseObjValAsArr js key with
| Except.ok xs => Array.mapM parser xs
| Except.error msg => Except.error $ msg





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
      let o1 := obj $ RBNode.erase Lean.strLt k1 kvs1;
      let o2 := obj $ RBNode.erase Lean.strLt k2 kvs2;
      isEqv o1 o2
    else 
      false
  | _,_ => false
| _, _ => false



end Lean.Json
