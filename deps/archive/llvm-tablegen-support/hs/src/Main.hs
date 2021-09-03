{-# Language OverloadedStrings #-}
module Main where

import System.Environment (getArgs)
import System.IO (Handle, stdout, withFile, IOMode(..))

import Control.Monad (guard, forM_, foldM)
import Control.Lens

import Data.Aeson
import Data.Aeson.Types (parse, Result(..), Parser)

import Data.Aeson.Lens

import Data.List (intersperse)
import Data.Monoid ((<>))

import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.ByteString.Lazy as B
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V

data Operand = Operand { {- name :: Text, -} pType :: Text }
  deriving Show

data Instruction =
  Instruction { inOperands :: [Operand]
              , outOperands :: [Operand]
              , classes :: [Text]
              }
  deriving Show

instance FromJSON Operand where
  parseJSON = withArray "operand" (go . V.toList)
    where
      go [ v, _n ] =
        Operand <$> {- withText "name" pure n
                <*> -} withObject "pType" (\obj -> obj .: "def" >>= withText "def" pure) v
      go _        = fail "expected 2 args"

-- "InOperandList": {
--     "args": [
--         [
--             {
--                 "def": "i64mem",
--                 "kind": "def",
--                 "printable": "i64mem"
--             },
--             "dst"
--         ],
--         [
--             {
--                 "def": "i64i32imm",
--                 "kind": "def",
--                 "printable": "i64i32imm"
--             },
--             "src"
--         ]
--     ],
--     "kind": "dag",
--     "operator": {
--         "def": "ins",
--         "kind": "def",
--         "printable": "ins"
--     },
--     "printable": "(ins i64mem:$dst, i64i32imm:$src)"
-- },

instance FromJSON Instruction where
  parseJSON v = do let classes = v ^.. key "!superclasses" . values . _String
                   guard (elem "Instruction" classes)
                   Instruction <$> getOps "InOperandList" <*> getOps "OutOperandList" <*> pure classes
    where
      getOps n = do Just args  <- return (v ^? key n . key "args")
                    withArray "operands" (mapM parseJSON . V.toList) args

tagName :: Value -> String
tagName v =
  case v of
    Object _ -> "Object"
    Array  _ -> "Array"
    String _ -> "String"
    Number _ -> "Number"
    Bool   _ -> "Bool"
    Null     -> "Null"

fullInsnEnumName :: Text -> Text
fullInsnEnumName n = "llvm::X86::" <> n

fullOperandEnumName :: Text -> Text
fullOperandEnumName n = "llvm::X86::DAGOperands::" <> n

-- Returns all instructions in the order that LLVM uses
instancesOf :: Text -> Value -> [Text]
instancesOf n v = v ^.. key "!instanceof" . key n . values . _String

allInstructions :: Value -> [Text]
allInstructions = instancesOf "Instruction"

allOperands :: Value -> [Text]
allOperands v = instancesOf "DAGOperand" v ++ instancesOf "PointerLikeRegClass" v

doInstruction :: Value -> Int -> Text -> Either String (Text, Text, Int)
doInstruction v nextIdx insnN =
  case fromJSON <$> v ^? key insnN of
    Just (Success insn) -> Right (insnArr, opArr, nextIdx + nOperands)
      where
      -- FIXME: we ignore outOperands for the moment, as they are broken for e.g. ADC
        operands  = outOperands insn ++ inOperands insn
        nOperands = length operands
        comment   = "    /* " <> insnN <> " */"
        insnArr   =  comment <> "[" <> fullInsnEnumName insnN <> "] = {"
                     <> T.pack (show nOperands) <> ", " <> T.pack (show nextIdx) <> "},"
        opArr     =  comment <> T.concat (map (\op -> fullOperandEnumName (pType op) <> ", ") operands)
    Just (Error err) -> Left (T.unpack insnN ++ ": " ++ err)
    _ -> Left ("Unknown instruction: " ++ T.unpack insnN)

-- We need pointer to array literals, which we can't easily make, so
-- follow LLVM and have a big array and store indicies into it.  The
-- HashMap doesn't guarantee the order of keys, so we use the
-- alphabetical list from the JSON.
doAllInstructions :: Value -> [Text] -> Either String (Text, Text)
doAllInstructions v insns =
  (\(i, o, _) -> (i, o)) <$> foldM go ("", "", 0) insns
  where
    go (i, o, n) insn = do (i', o', n') <- doInstruction v n insn
                           return (i <> "\n" <> i', o <> "\n" <> o', n')

emitArrays :: Handle -> Text -> Text -> Text -> Text -> Value -> IO ()
emitArrays hdl iArrN oArrN oNArrN assertN v = do
  (iArrT, oArrT) <- case doAllInstructions v insns of
                      Right x -> return x
                      Left err -> error err
  emitEnum
  emitArr iArrN iArrT
  emitArr oArrN oArrT
  let oNArrT = T.concat (intersperse ",\n" (map (\o -> "    \"" <> o <> "\"") ops))
  emitArr oNArrN oNArrT
  where
    insns = allInstructions v
    ops   = allOperands v ++ ["unknown", "variable_ops"] -- also appears.
    emitArr n txt = T.hPutStrLn hdl (n <> "[] = {\n" <> txt <> "\n};")
    emitEnum = do T.hPutStrLn hdl "namespace llvm {\nnamespace X86 {\nnamespace DAGOperands {\n enum DAGOperandType {"
                  forM_ (zip [0..] ops) $ \(opIdx, opN) ->
                    T.hPutStrLn hdl ("    " <> opN <> " = " <> T.pack (show opIdx) <> ",")
                  T.hPutStrLn hdl "};\n} // namespace DAGOperands\n} // namespace X86\n} // namespace llvm"

fileToMap :: FilePath -> Handle -> IO ()
fileToMap file hdl  = do
  bs <- B.readFile file
  case decode bs :: Maybe Value of
    Nothing -> error "No parse"
    Just v  -> emitArrays hdl "static struct operand_desc iArr"
                              "static llvm::X86::DAGOperands::DAGOperandType oArr"
                              "static const char * oNArr"
                              "void checkAssumptions"
                              v

instructions :: Value -> Result (H.HashMap Text Instruction)
instructions = parse (withObject "Toplevel" go)
  where
    go = pure . H.mapMaybe toInstruction
    toInstruction = fromResult . parse parseJSON
    fromResult (Error _)   = Nothing
    fromResult (Success r) = Just r
                              
main :: IO ()
main = do
  [outfile, file] <- getArgs
  withFile outfile WriteMode (fileToMap file)


  
