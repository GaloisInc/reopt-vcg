

namespace SMT

private def reservedIdList : List String :=
[
"Array",
"BitVec",
"and",
"benchmark",
"bit1",
"bv",
"bvadd",
"bvand",
"bvashr",
"bvcomp",
"bvlshr",
"bvmul",
"bvnand",
"bvneg",
"bvnor",
"bvnot",
"bvor",
"bvsdiv",
"bvsge",
"bvsgt",
"bvshl",
"bvsle",
"bvslt",
"bvsmod",
"bvsrem",
"bvsub",
"bvudiv",
"bvuge",
"bvugt",
"bvule",
"bvult",
"bvurem",
"bvxnor",
"bvxor",
"concat",
"distinct",
"exists",
"extract",
"false",
"flet",
"forall",
"if_then_else",
"iff",
"implies",
"let",
"not",
"or",
"repeat",
"rotate_left",
"rotate_right",
"sat",
"select",
"sign_extend",
"store",
"theory",
"true",
"unknown",
"unsat",
"xor",
"zero_extend",
"Constant",
"InputVariable",
"LocalVariable",
"NaN",
"RNA",
"RNE",
"RTN",
"RTP",
"RTZ",
"Variable",
"and",
"as",
"assert",
"assert-propagation",
"assert-reduction",
"assert-rewrite",
"bv2nat",
"check-sat",
"check-sat-assuming",
"check-synth",
"const",
"constraint",
"declare-codatatype",
"declare-codatatypes",
"declare-const",
"declare-datatype",
"declare-datatypes",
"declare-fun",
"declare-funs",
"declare-heap",
"declare-preds",
"declare-primed-var",
"declare-sort",
"declare-sorts",
"declare-var",
"define",
"define-const",
"define-fun",
"define-fun-rec",
"define-funs-rec",
"define-sort",
"distinct",
"divisible",
"echo",
"emp",
"emptyset",
"exists",
"exit",
"extract",
"forall",
"get-assertions",
"get-assignment",
"get-info",
"get-model",
"get-option",
"get-proof",
"get-qe",
"get-qe-disjunct",
"get-unsat-assumptions",
"get-unsat-core",
"get-value",
"include",
"inst-closure",
"int2bv",
"inv-constraint",
"is",
"ite",
"lambda",
"let",
"match",
"meta-info",
"mkTuple",
"not",
"or",
"par",
"pop",
"push",
"repeat",
"reset",
"reset-assertions",
"rotate_left",
"rotate_right",
"roundNearestTiesToAway",
"roundNearestTiesToEven",
"roundTowardNegative",
"roundTowardPositive",
"roundTowardZero",
"set-info",
"set-logic",
"set-option",
"set-options",
"sign_extend",
"simplify",
"synth-fun",
"synth-inv",
"to_fp",
"to_fp_bv",
"to_fp_fp",
"to_fp_real",
"to_fp_signed",
"to_fp_unsigned",
"tupSel",
"univset",
"xor",
"zero_extend",
"cnf",
"fof",
"include",
"tff",
"thf",
"type",
"=", 
">=", 
"<=", 
"+", 
"-", 
"*", 
">", 
"<", 
"!="
]

private def reservedIdTable : PHashMap String Unit := reservedIdList.foldl (λ m kw => m.insert kw ()) PersistentHashMap.empty

private def isReservedId (x:String) : Bool := reservedIdTable.contains x

-- Map of normalized suggested names to the number of times they've
-- been previously requested to expidite fresh name generation.
structure IdGen :=
(usedIds : PHashMap String Nat)

namespace IdGen

private def normalizeSuggestedName (s:String) : String :=
let s' := (s.data.filter (λ (c:Char) => !c.isWhitespace)).asString;
if s'.isEmpty
then "_"
else s'

private def addSuffix (origStr : String) (n : Nat) : String :=
match (origStr.takeRight 1).data with
| [c] => if c.isDigit then origStr ++ "_" ++ (repr n) else origStr ++ (repr n)
| _ => origStr ++ (repr n)

private partial def genIdAux (idGen : IdGen) : String → Option Nat → (String × Nat)
| name, none => if idGen.usedIds.contains name || isReservedId name
                then genIdAux name (some 0)
                else (name, 0)
| namePrefix, some n =>
  let nameN := addSuffix namePrefix n;
  if idGen.usedIds.contains nameN
  then genIdAux namePrefix (some (n + 1))
  else (nameN, n + 1)

/-- Generate a fresh symbol in the monad, if possible simply using the suggested string.  --/
def genId (idGen : IdGen) (suggestedName : String) : (IdGen × String) :=
  let sym := normalizeSuggestedName suggestedName;
  let prevOccurrences := idGen.usedIds.find? sym;
  let (name, tries) := genIdAux idGen sym prevOccurrences;
  (⟨idGen.usedIds.insert sym tries⟩, name)


def empty : IdGen := IdGen.mk PersistentHashMap.empty

end IdGen

end SMT
