{-# LANGUAGE DataKinds, TypeFamilies, GADTs #-}

module Main where

import Data.Word
import System.Environment 
  
import qualified Data.ByteString as B

import Trace.X86

main :: IO ()
main = do
  [elffile, trfile] <- getArgs
  elfbs <- B.readFile elffile
  trbs  <- B.readFile trfile  
  case parseTrace elfbs trbs of
    Left err -> print err
    Right tr -> mapM_ print tr
