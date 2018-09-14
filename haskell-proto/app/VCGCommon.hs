{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module VCGCommon
  ( SymBV64
  , Ptr
  , BaseBV64Type
  , newUserSymbol
  , bv64
  , nat64
  , warning
  , fatalError
  , SymMemory
  , readMemBVLE
  , writeMemBVLE
  ) where

import Control.Monad
import Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import           Data.Proxy
import GHC.Stack
import System.Exit
import System.IO

import What4.Symbol
import What4.Interface

warning :: String -> IO ()
warning msg = do
  hPutStrLn stderr ("Warning: " ++ msg)

fatalError :: String -> IO a
fatalError msg = do
  hPutStrLn stderr msg
  exitFailure

newUserSymbol :: HasCallStack => String -> SolverSymbol
newUserSymbol str =
  case userSymbol str of
    Left err -> error $ str ++ ": " ++ (ppSolverSymbolError err)
    Right ssym -> ssym

nat64 :: NatRepr 64
nat64 = knownNat

bv64 :: BaseTypeRepr (BaseBVType 64)
bv64 = BaseBVRepr nat64

--type BaseBV8Type = BaseBVType 8
type BaseBV64Type = BaseBVType 64

--type SymBVByte sym = SymBV sym 8
type SymBV64 sym = SymBV sym 64

type Ptr sym = SymBV64 sym -- TODO: distinguish Ptr and SymBV64 at type level

type SymMemory sym = SymArray sym (EmptyCtx ::> BaseBVType 64) (BaseBVType 8)

-- | Read a number of bytes as a bitvector.
readMemBVLE :: forall sym w
            .  (IsExprBuilder sym, 1 <= w)
            => sym
            -> SymMemory sym --
            -> Ptr sym -- ^ Address to read
            -> NatRepr w-- ^ Number of bytes to read.
            -> IO (SymExpr sym (BaseBVType (8*w)))
readMemBVLE sym mem ptr0 w = do
  one <- bvLit sym (knownNat @64) 1
  let go :: forall u
         .  (1 <= u)
         => SymBV sym u -- Previous value
         -> Ptr sym -- Pointer
         -> Integer -- Number of bytes left
         -> IO (Some (SymExpr sym))
      go prev ptr cnt
        | cnt <= 0 = pure $! Some prev
        | otherwise = do
            readByte <- arrayLookup sym mem (Ctx.singleton ptr)
            prev' <- bvConcat sym readByte prev
            ptr' <- bvAdd sym ptr one
            LeqProof <- pure $ leqAddPos (Proxy @8) (Proxy @u)
            go prev' ptr' (cnt-1)
  firstVal <- arrayLookup sym mem (Ctx.singleton ptr0)
  Some v <- go firstVal ptr0 (natValue w-1)
  let w8 = natMultiply (knownNat @8) w
  Just LeqProof <- pure $ testLeq (knownNat @1) w8
  Just Refl <- pure $ testEquality (exprType v) (BaseBVRepr w8)
  pure $! v

-- | Read a number of bytes as a bitvector.
writeMemBVLE :: forall sym w
            .  (IsExprBuilder sym)
            => sym
            -> SymMemory sym
            -> Ptr sym
            -> SymBV sym w
            -> IO (SymMemory sym)
writeMemBVLE sym mem0 ptr0 val = do
  one <- bvLit sym (knownNat @64) 1
  let w = bvWidth val
  when (natValue w `mod` 8 /= 0) $ do
    error "writeMemBVLE expects width to be a multiple of 8."
  let byteCount = natValue w `div` 8
  let go :: SymMemory sym
         -> Ptr sym -- Pointer
         -> NatRepr u -- Offset to write
         -> IO (SymMemory sym)
      go mem ptr idx
        | natValue idx >= byteCount = pure $! mem
        | otherwise = do
            let idx' = addNat idx (knownNat @8)
            Just LeqProof <- pure $ testLeq idx' w
            byte <- bvSelect sym idx (knownNat @8) val
            mem' <- arrayUpdate sym mem (Ctx.singleton ptr) byte
            ptr' <- bvAdd sym ptr one
            go mem' ptr' idx'
  go mem0 ptr0 (knownNat @0)
