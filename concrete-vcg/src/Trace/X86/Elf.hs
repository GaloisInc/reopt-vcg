
module Trace.X86.Elf (Symtab(..), symtab) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as B

import Data.ElfEdit
import qualified Data.Vector as V
import Data.Word

import qualified Data.IntervalMap as IM

type Symtab = IM.IntervalMap Word64 ByteString

symtab :: ByteString -> Either String Symtab
symtab bs = do
  case parseElf bs of
    Elf64Res [] elf -> do
      let sym_assocs = [ (IM.IntervalCO (steValue ste) (steValue ste + steSize ste), steName ste)
                       | let [est] = elfSymtab elf
                       , ste <- V.toList (elfSymbolTableEntries est)
                       , steIndex ste /= SHN_UNDEF
                       , steType ste == STT_FUNC
                       ]
      return (IM.fromList sym_assocs)
    _ -> Left "???"
