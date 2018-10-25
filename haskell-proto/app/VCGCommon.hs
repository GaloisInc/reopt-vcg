{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module VCGCommon
  ( {-
    SymBV64
  , Ptr
  , BaseBV64Type
  , newUserSymbol
  , bv64
  , nat64
  , SymMemory
  , readMemBVLE
  , writeMemBVLE
-}
    -- * SMT
    Var
  , varTerm
    -- * Memory
  , readBVLE
  , writeBVLE
    -- * Error reporting
  , warning
  , fatalError
  ) where

import           Data.Text (Text)
import qualified Data.Text.Lazy.Builder as Builder
import           System.Exit
import           System.IO
import qualified What4.Protocol.SMTLib2.Syntax as SMT

type Var = Text

varTerm :: Var -> SMT.Term
varTerm = SMT.T . Builder.fromText

-- | Read a number of bytes as a bitvector.
-- Note. This refers repeatedly to ptr so, it should be a constant.
readBVLE :: SMT.Term -- ^ Memory
         -> SMT.Term  -- ^ Address to read
         -> Integer -- ^ Number of bytes to read.
         -> SMT.Term
readBVLE mem ptr0 w = go (w-1)
  where go :: Integer -> SMT.Term
        go 0 = SMT.select mem ptr0
        go i =
          let ptr = SMT.bvadd ptr0 [SMT.bvdecimal i 64]
           in SMT.concat (SMT.select mem ptr) (go (i-1))

-- | Read a number of bytes as a bitvector.
-- Note. This refers repeatedly to ptr so, it should be a constant.
writeBVLE :: SMT.Term
          -> SMT.Term  -- ^ Address to write
          -> SMT.Term  -- ^ Value to write
          -> Integer -- ^ Number of bytes to write.
          -> SMT.Term
writeBVLE mem ptr0 val w = go (w-1)
  where go :: Integer -> SMT.Term
        go 0 = SMT.store mem ptr0 (SMT.extract 7 0 val)
        go i =
          let ptr = SMT.bvadd ptr0 [SMT.bvdecimal i 64]
           in SMT.store (go (i-1)) ptr (SMT.extract (8*i+7) (8*i) val)


warning :: String -> IO ()
warning msg = do
  hPutStrLn stderr ("Warning: " ++ msg)

fatalError :: String -> IO a
fatalError msg = do
  hPutStrLn stderr msg
  exitFailure
