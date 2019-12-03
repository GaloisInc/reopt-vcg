
module Trace.X86 (TraceEvent (..), TraceElem(..), parseTrace) where

import Numeric (showHex)

import Data.Word
import qualified Data.IntervalMap.Strict as IM
import Data.IntervalMap.Generic.Interval as IM


import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Data.Maybe (maybe)

import Trace.X86.Parser (TraceEvent (..))
import qualified Trace.X86.Parser as Parser
import Trace.X86.Elf

data TraceElem =
  TraceElem { traceIP        :: !Word64
            , traceEvent     :: !TraceEvent
            , traceSym       :: !(Maybe (ByteString, Integer))
            } deriving Show

resolveElem :: Symtab -> (Word64, TraceEvent) -> TraceElem
resolveElem syms (ip, ev) =
  TraceElem ip ev sym 
  where
    sym = case IM.toList (syms `IM.containing` ip) of
            (base, s) : _ -> Just (s, toInteger (ip - IM.lowerBound base))
            _             -> Nothing
    
parseTrace :: ByteString -> ByteString -> Either String [TraceElem]
parseTrace elfbs trbs = do
  syms <- symtab elfbs
  tr   <- Parser.parseTrace trbs
  return (map (resolveElem syms) tr)
  

