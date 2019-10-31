
module Trace.X86 (TraceEvent (..), TraceElem(..), parseTrace) where

import Numeric (showHex)

import Data.Word
import qualified Data.IntervalMap.Strict as IM

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Data.Maybe (maybe)

import Trace.X86.Parser (TraceEvent (..))
import qualified Trace.X86.Parser as Parser
import Trace.X86.Elf

data TraceElem =
  TraceElem { traceIP    :: !Word64
            , traceEvent :: !TraceEvent
            , traceSym   :: !(Maybe ByteString)
            } deriving Show

resolveElem :: Symtab -> (Word64, TraceEvent) -> TraceElem
resolveElem syms (ip, ev) =
  TraceElem ip ev $ case IM.elems (syms `IM.containing` ip) of
                      s : _ -> Just s
                      _     -> Nothing
    
parseTrace :: ByteString -> ByteString -> Either String [TraceElem]
parseTrace elfbs trbs = do
  syms <- symtab elfbs
  tr   <- Parser.parseTrace trbs
  return (map (resolveElem syms) tr)
  

