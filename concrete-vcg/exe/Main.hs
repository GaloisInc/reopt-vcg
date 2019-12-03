{-# LANGUAGE DataKinds, TypeFamilies, GADTs, OverloadedStrings #-}

module Main where

import Numeric (showHex)
import Data.Word
import System.Environment 
  
import qualified Data.ByteString.Char8 as B

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint hiding ((<>))

import Trace.X86

main :: IO ()
main = do
  [elffile, trfile] <- getArgs
  elfbs <- B.readFile elffile
  trbs  <- B.readFile trfile  
  case parseTrace elfbs trbs of
    Left err -> print err
    Right tr -> do
      let (syms, ips, evs) = unzip3 (map ppTraceElem tr)
          syms' = map show syms
          symL  = maximum (map length syms')
          ips'  = map show ips
          ipL   = maximum (map length ips')
          d     = vcat (zipWith3 (\sym ip ev -> text sym $$ (nest (symL + 1) ((text ip) $$ nest (ipL + 1) ev))) syms' ips' evs)
      print d


hex x = "0x" <> text (showHex x "")

ppTraceElem :: TraceElem -> (Doc, Doc, Doc)
ppTraceElem te = (sym, hex (traceIP te), ppTraceEvent (traceEvent te))
  where
    sym = case traceSym te of
      Nothing -> text ""
      Just (s, o) -> text (B.unpack s) <> "+" <> hex o

ppTraceEvent :: TraceEvent -> Doc
ppTraceEvent (Syscall n args)   = "SYSCALL<" <> int n <> ">" <> parens (hcat (punctuate "," (map hex args)))
ppTraceEvent (Read ptr n v)     = "READ"     <+> hex ptr <+> hex v
ppTraceEvent (Write ptr n v)    = "WRITE"    <+> hex ptr <+> hex v
