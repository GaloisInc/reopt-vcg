{-# LANGUAGE DeriveGeneric #-}
module Reopt.VCG.Config
  ( MetaVCGConfig(..)
  , VCGFunInfo(..)
  ) where

import           Data.Word
import qualified Data.Yaml as Yaml
import           GHC.Generics

-- | Our VCG supports cases where each LLVM block corresponds to a contiguous range
-- of instructions.
data VCGBlockInfo = VCGBlockInfo
  { blockLabel :: !String
    -- ^ LLVM label of block
  , blockAddr :: !Word64
    -- ^ Address of start of block
  , blockSize :: !Word64
    -- ^ Number of bytes in block
  }
  deriving (Show, Generic)

instance Yaml.FromJSON VCGBlockInfo

data VCGFunInfo = VCGFunInfo
  { llvmFunName    :: String
    -- ^ LLVM function name
  , llvmArgs       :: [String]
    -- ^ The LLVM argument names
  , llvmStartBlock :: String
    -- ^ LLVM starting block name, either a digit (annonymous block) or a named block
  , llvmVars       :: [String]
    -- ^ LLVM mapping between immediate variables
  , macawFunName   ::  String
    -- ^ Macaw function name
  , macawArgs      :: [String]
    -- ^ Macaw argument names, build mappings with llvmArgs
  , macawVars      :: [String]
    -- ^ Macaw variables, build mappings with llvmVars
  , blocks :: [VCGBlockInfo]
    -- ^ Information relating blocks
  }
  deriving (Show, Generic)

instance Yaml.FromJSON VCGFunInfo

data MetaVCGConfig = MetaVCGConfig
  { llvmBCFilePath :: FilePath
    -- ^ LLVM .bc file path
  , binFilePath    ::  String
    -- ^ Binary file path that will be analyzed by Macaw
  , functions :: [VCGFunInfo]
  }
  deriving (Show, Generic)

instance Yaml.FromJSON MetaVCGConfig
