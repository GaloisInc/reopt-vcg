{-# LANGUAGE OverloadedStrings #-}

module Trace.X86.Parser (TraceEvent(..), parseTrace) where

import Data.Attoparsec.ByteString.Char8
import qualified Data.ByteString as BS

import Data.Bits 
import Data.Char (isHexDigit)
import Data.Word

-- The format from the simulator is something like
--
-- ip       op    addr           sz val
-- 0x201448 write 0x7fffffffffb8 64 0x20144d
-- and
-- ip        op     sysno, #args, args
-- 0x20112d syscall 1 3 0x1 0x204950 0x11

-- From the lean
-- inductive trace_event 
--   | syscall : Nat -> List machine_word -> trace_event
--   | read    : machine_word -> ∀(n:Nat), bitvec n -> trace_event
--   | write   : machine_word -> ∀(n:Nat), bitvec n -> trace_event
data TraceEvent =
  Syscall Int [Word64] | Read Word64 Int Integer | Write Word64 Int Integer
  deriving Show

hexP :: (Integral a, Bits a) => Parser a
hexP = "0x" *> hexadecimal

tokenP :: Parser a -> Parser a
tokenP p = p <* (choice [ space >> skipSpace , endOfInput ])

syscallP, readP, writeP :: Parser TraceEvent

syscallP = do tokenP "syscall"
              sysNum <- tokenP decimal
              num    <- tokenP decimal
              args   <- count num (tokenP hexP)
              return (Syscall sysNum args)

readP  = tokenP "read"  *> (Read  <$> tokenP hexP <*> tokenP decimal <*> tokenP hexP)
writeP = tokenP "write" *> (Write <$> tokenP hexP <*> tokenP decimal <*> tokenP hexP)

eventP :: Parser (Word64, TraceEvent)
eventP = do
  (,) <$> tokenP hexP <*> choice [ syscallP, readP, writeP ]
  
parseTrace :: BS.ByteString -> Either String [(Word64, TraceEvent)]
parseTrace = parseOnly (many' eventP)
