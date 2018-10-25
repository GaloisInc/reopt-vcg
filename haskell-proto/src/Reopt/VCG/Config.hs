{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Reopt.VCG.Config
  ( MetaVCGConfig(..)
  , VCGFunInfo(..)
  , VCGBlockInfo(..)
  , BlockEvent(..)
  , BlockEventType(..)
  ) where

import qualified Data.HashMap.Strict as HMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import           Data.Text (Text)
import           Data.Word
import           Data.Yaml ((.:))
import qualified Data.Yaml as Yaml
import           GHC.Generics

------------------------------------------------------------------------
-- JSON utilities

-- | A list of valid fields for an object.
type FieldList = HashSet Text

-- | Create a field list from a list
fields :: [Text] -> FieldList
fields = HSet.fromList

-- | Parse a YAML and fail if our fields are wrong.
withFixedObject :: String -> FieldList -> (Yaml.Object -> Yaml.Parser a) -> Yaml.Value -> Yaml.Parser a
withFixedObject nm flds f (Yaml.Object o) =
  case HMap.foldrWithKey badFields [] o of
    [] -> f o
    l -> fail $ "Unexpected fields in " ++ nm ++ ": " ++ show l
  where badFields :: Text -> Yaml.Value -> [Text] -> [Text]
        badFields f _ l =
          if HSet.member f flds then
            l
           else
            f:l


------------------------------------------------------------------------
-- Block declarations

data BlockEventType
   = StackRegRead
   | StackRegWrite
  deriving (Show)

instance Yaml.FromJSON BlockEventType where
  parseJSON (Yaml.String "stack_reg_read")  = pure StackRegRead
  parseJSON (Yaml.String "stack_reg_write") = pure StackRegWrite
  parseJSON v = fail $ "Expected block event type, encountered " ++ show v

data BlockEvent = BlockEvent
  { eventAddr :: !Integer
  , eventType :: !BlockEventType
  }
  deriving (Show)


blockEventFields :: FieldList
blockEventFields = fields ["addr", "type"]

instance Yaml.FromJSON BlockEvent where
  parseJSON = withFixedObject "BlockEvent" blockEventFields $ \v ->
    BlockEvent
      <$> v .: "addr"
      <*> v .: "type"

-- | Our VCG supports cases where each LLVM block corresponds to a contiguous range
-- of instructions.
data VCGBlockInfo = VCGBlockInfo
  { blockLabel :: !String
    -- ^ LLVM label of block
  , blockAddr :: !Word64
    -- ^ Address of start of block
  , blockSize :: !Word64
    -- ^ Number of bytes in block
  , blockEvents :: ![BlockEvent]
  }
  deriving (Show, Generic)


blockInfoFields :: FieldList
blockInfoFields = fields ["label", "addr", "size", "events"]

instance Yaml.FromJSON VCGBlockInfo where
  parseJSON = withFixedObject "BlockInfo" blockInfoFields $ \v ->
    VCGBlockInfo
      <$> v .: "label"
      <*> v .: "addr"
      <*> v .: "size"
      <*> v .: "events"

data VCGFunInfo = VCGFunInfo
  { llvmFunName    :: !String
    -- ^ LLVM function name
  , macawFunName   :: !String
    -- ^ Macaw function name
  , stackSize :: !Integer
    -- ^ Number of bytes in binary stack size.
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

--  , llvmArgs       :: [String]
    -- ^ The LLVM argument names
--  , llvmStartBlock :: String
    -- ^ LLVM starting block name, either a digit (annonymous block) or a named block
--  , llvmVars       :: [String]
    -- ^ LLVM mapping between immediate variables
--  , macawArgs      :: [String]
    -- ^ Macaw argument names, build mappings with llvmArgs
