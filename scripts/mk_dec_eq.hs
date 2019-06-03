
module MkDecEq where

import Data.List

type Type = [ (String, [Bool]) ]

-- (ctore_name, args (True == is recursive))
ctors =
  [ ("bv", [False])
  , ("bit", [])
  , ("float", [])
  , ("double", [])
  , ("x86_80", [])
  , ("vec", [False, True])
  , ("pair", [True, True])
  , ("fn"  , [True, True]) ]

-- We need to produce two types of equation --- recursive and mismatch.  The mismatch cases are simple,
-- if tedious, while the recursive cases are a bit trickier

mismatch :: String -> Type -> [String]
mismatch tname cons = [ doOne x y | x <- cons, y <- cons, x /= y ]
  where
    noConf = "isFalse (λh, " ++ tname ++ ".noConfusion h)"
    underscores c 0 = c
    underscores c n = "(" ++ c ++ " " ++ intercalate " " (replicate n "_") ++ ")"
    doOne (c1, args1) (c2, args2) = "| "   ++ underscores c1 (length args1)
                                    ++ " " ++ underscores c2 (length args2)
                                    ++ " := " ++ noConf

recursive :: String -> Type -> String -> [String]
recursive tname cons recName = map doOne cons
  where
    ctor (c, [])   _   = c -- never called, included for completeness
    ctor (c, args) sfx = "(" ++ c ++ " " ++ intercalate " " (map (\n -> "c" ++ show n ++ sfx) [1 .. length args]) ++ ")"
    doOne (n, [])      = "| " ++ n ++ " " ++ n ++ " := isTrue rfl"
    doOne c@(_, args)  = "| " ++ ctor c "" ++ " " ++ ctor c "'" ++ " := "
                         ++ "\n (" ++ match c ++ "\n"
                         ++ trueMatch (length args) ++ "\n"
                         ++ intercalate "\n" (map (falseMatch (length args)) [1 .. length args]) ++ ")"
    
    match (c, cs)    = "match " ++ intercalate ", " (zipWith oneHdr cs [1..]) ++ " with "
    oneHdr b n = (if b then recName else "decEq") ++ " c" ++ show n ++ " c" ++ show n ++ "'"
    
    hyps n sfx = map (\n -> "h" ++ show n ++ sfx) [1..n]
    trueMatch n      =
      "  | " ++ intercalate ", " (map (\h -> "(isTrue " ++ h ++ ")") (hyps n "")) ++ " := "
             ++ "isTrue (" ++ intercalate " ▸ " (hyps n "" ++ ["rfl"]) ++ ")"

    falseMatch n pos = "  | "
      ++ intercalate ", " (replicate (pos - 1) "(isTrue _)" ++ ["(isFalse nh)"] ++ (replicate (n - pos) "_"))
      ++ " := " ++ noConf n pos
    noConf n pos = "isFalse (λh, " ++ tname ++ ".noConfusion h $ λ"
                   ++ intercalate " " (hyps n "'") ++ ", absurd h" ++ show pos ++ "' nh)"

mkDecEq :: String -> Type -> String -> String
mkDecEq tname cons recName =
  "protected def " ++ recName ++ " : Π(e e' : " ++ tname ++ "), Decidable (e = e')\n"
  ++ intercalate "\n" (recursive tname cons recName ++ mismatch tname cons)

  
