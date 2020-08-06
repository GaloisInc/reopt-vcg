-- This utility throws away definitions and declarations which do not appear in assertions.
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import           Control.Applicative ((<|>))
import           System.Environment(getArgs)
import           System.IO (stderr, hPutStrLn)
import           System.Exit (exitFailure)
import qualified Data.Map as Map
import           Data.Map (Map)
import qualified Data.Set as Set
import           Data.Set (Set)

import           Control.Monad.State

import           Data.Char (isAlphaNum, isDigit)

import           Text.Parsec (many1, satisfy)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import           Data.Text (Text, pack)

import           Text.Parsec (anyChar, char, digit, many, many1, manyTill, newline, satisfy, string
                             , choice, hexDigit, try)
import           Text.Parsec.Text (Parser)

import           Data.SCargot
import           Data.SCargot.Repr
import           Data.SCargot.Repr.Basic
import           Data.SCargot.Comments

main :: IO ()
main = do
  [file] <- getArgs
  bs     <- Text.readFile file
  case decode smtParser bs of
    Left err -> hPutStrLn stderr err *> exitFailure
    Right vs -> Text.putStrLn  (encode smtPrinter (strip vs))
       -- Text.putStrLn  (encode smtPrinter vs)

strip :: [SExpr Atom] -> [SExpr Atom]
strip vs = filter (filterOne (required s)) vs
  where
    s = execState (mapM_ scanOne vs) (DepState Set.empty Map.empty)

-- Analysis
data DepState = DepState
  { required :: Set Text
  , deps     :: Map Text (Set Text)
  }

type DepM = State DepState


freeIn :: SExpr Atom -> Set Text
freeIn Nil        = Set.empty
freeIn (A x)      = go x 
  where
    go (Symbol s) = Set.singleton s
    go _          = Set.empty
freeIn (x ::: xs) = freeIn x `Set.union` freeIn xs


handleAssert (Set.minView -> Just (v, rest)) s
  | v `elem` required s = handleAssert rest s
  | otherwise = handleAssert (rest `Set.union` (Map.findWithDefault Set.empty v (deps s)))
                             (s { required = Set.insert v (required s) })
handleAssert _ s = s

scanOne :: SExpr Atom -> DepM ()
scanOne (A (Command "assert") ::: p ::: Nil) = modify (handleAssert (freeIn p))
scanOne (A (Command "check-sat-assuming") ::: L ps ::: Nil) = mapM_ (modify . handleAssert . freeIn) ps                    
scanOne (A (Command "define-fun") ::: A (Symbol f) ::: args ::: _ ::: body) = do
--  let Right argVs = asAssoc (Right . map fst) args
  let ds          = freeIn body -- FIXME `Set.difference` (Set.fromList argVs)
  modify (\s -> s { deps = Map.insert f ds (deps s) })
scanOne (A (Command "define-fun-rec") ::: A (Symbol f) ::: args ::: _ ::: body) = do
--  let Right argVs = asAssoc (Right . map fst) args
  let ds          = freeIn body -- FIXME `Set.difference` (Set.fromList argVs)
  modify (\s -> s { deps = Map.insert f ds (deps s) })  
scanOne (A (Command "define-const") ::: A (Symbol f) ::: _ ::: body) = do
  let ds           = freeIn body
  modify (\s -> s { deps = Map.insert f ds (deps s) })
scanOne _ = pure ()

filterOne :: Set Text -> SExpr Atom -> Bool
filterOne ds (A (Command "define-fun") ::: A (Symbol f) ::: _) = f `Set.member` ds
filterOne ds (A (Command "define-fun-rec") ::: A (Symbol f) ::: _) = f `Set.member` ds
filterOne ds (A (Command "declare-fun") ::: A (Symbol f) ::: _) = f `Set.member` ds
filterOne ds (A (Command "define-const") ::: A (Symbol f) ::: _) = f `Set.member` ds
filterOne ds (A (Command "declare-const") ::: A (Symbol f) ::: _) = f `Set.member` ds
filterOne _ _ = True

-- Parsing atoms (c.f. What4.Protocol.SMTLib2.Parse)

smtParser :: SExprParser Atom (SExpr Atom)
smtParser = withLispComments (mkParser pAtom)

smtPrinter :: SExprPrinter Atom (SExpr Atom)
smtPrinter = flatPrint sAtom

data Atom = Command Text | Builtin Text | Reserved Text | Symbol Text | Number Text
  deriving (Eq, Ord, Show)

pAtom :: Parser Atom
pAtom =  ((Command   . pack) <$> (choice (map (try . string) commandNames)))
     <|> ((Reserved  . pack) <$> (choice (map (try . string) generalReservedWords)))
     <|> ((Builtin   . pack) <$> (choice (map (try . string) builtinWords)))

     <|> ((Symbol    . pack) <$> pSymbol)         
     <|> ((Number    . pack) <$> (((:) <$> char '#' <*> (hexP <|> binP))
                                   <|> many1 digit))
  where
    hexP = (:) <$> char 'x'  <*> many1 hexDigit
    binP = (:) <$> char 'b' <*> many1 (char '0' <|> char '1')
           

sAtom :: Atom -> Text
sAtom atom =
  case atom of
    Command t -> t
    Reserved t -> t
    Builtin  t -> t
    Symbol t -> t
    Number t -> t

pSymbol :: Parser String
pSymbol = pKeyword <|> pSimple <|> pQuoted
  where
    pKeyword = (:) <$> char ':' <*> pSimple
    
    pSimple = ((:) <$> satisfy (\c -> isSimpleSymChar c && not (isDigit c))
                                   <*> many (satisfy isSimpleSymChar))
    pQuoted = do char '|'
                 b <- many1 (satisfy (/= '|'))
                 char '|'
                 return ("|" ++ b ++ "|")

isSimpleSymChar :: Char -> Bool
isSimpleSymChar c = isAlphaNum c || c `elem` ("~!@$%^&*_-+=<>.?/" :: String)

builtinWords :: [String]
builtinWords =
  [ "=" ]

generalReservedWords :: [String]
generalReservedWords = 
  [ "!"
  , "_"
  , "as"
  , "BINARY"
  , "DECIMAL"
  , "exists"
  , "HEXADECIMAL"
  , "forall"
  , "let"
  , "match"
  , "NUMERAL"
  , "par"
  , "STRING"
  ]

commandNames :: [String]
commandNames = 
  [ "assert"
  , "check-sat-assuming"
  , "check-sat"
  , "declare-const"
  , "declare-datatypes"
  , "declare-datatype"
  , "declare-fun"
  , "declare-sort"
  , "define-fun-rec"
  , "define-fun"
  , "define-sort"
  , "echo"
  , "exit"
  , "get-assertions"
  , "get-assignment"
  , "get-info"
  , "get-model"
  , "get-option"
  , "get-proof"
  , "get-unsat-assumptions"
  , "get-unsat-core"
  , "get-value"
  , "pop"
  , "push"
  , "reset"
  , "reset-assertions"
  , "set-info"
  , "set-logic"
  , "set-option"
  ]
