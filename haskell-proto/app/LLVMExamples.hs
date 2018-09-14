{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module LLVMExamples
  ( simpleCall
  , simpleArith
  , multiBlocks
  ) where

import Text.LLVM hiding ((:>))

simpleCall :: Module
simpleCall = snd $ runLLVM $ do
  f <- define emptyFunAttrs (iT 64) "callee" voidT $ \_x -> do
    a <- alloca (iT 64) Nothing (Just 8)
    store (int 42) a (Just 8)
    b <- load a (Just 8)
    ret b
  define emptyFunAttrs voidT "caller" voidT $ \_x -> do
    _a <- alloca (iT 64) Nothing (Just 8)
    _b <- call f []
    retVoid

simpleArith :: Module
simpleArith = snd $ runLLVM $ do
  define emptyFunAttrs (iT 64) "g" voidT $ \_x -> do
    a  <- alloca (iT 64) Nothing (Just 8)
    store (int 3) a (Just 8)
    b  <- alloca (iT 64) Nothing (Just 8)
    store (int 4) b (Just 8)
    a' <- load a (Just 8)
    b' <- load b (Just 8)
    c  <- add a' b'
    ret c

multiBlocks :: Module
multiBlocks = snd $ runLLVM $ do
  define emptyFunAttrs (iT 64) "f" voidT $ \_x -> do
    a  <- alloca (iT 64) Nothing (Just 8)
    store (int 3) a (Just 8)
    b  <- alloca (iT 64) Nothing (Just 8)
    store (int 4) b (Just 8)
    jump "nextblk"
    a' <- load a (Just 8)
    b' <- load b (Just 8)
    c  <- add a' b'
    ret c
