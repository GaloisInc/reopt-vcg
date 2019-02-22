{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Reopt.VCG.Config
  ( MetaVCGConfig(..)
  , VCGFunInfo(..)
  , VCGBlockInfo(..)
  , AllocaInfo(..)
  , AllocaName(..)
  , BlockEvent(..)
  , BlockEventInfo(..)
  ) where

import qualified Data.HashMap.Strict as HMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import           Data.Scientific (toBoundedInteger)
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
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

-- | Parse a YAML and fail if there are any fields not in the set.
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
-- AllocaInfo

-- | Identifier associated with an LLVM allocation.
newtype AllocaName = AllocaName { allocaNameText :: Text }
  deriving (Eq, Ord)

instance IsString AllocaName where
  fromString = AllocaName . Text.pack

instance Show AllocaName where
  show (AllocaName nm) = Text.unpack nm

instance Yaml.FromJSON AllocaName where
  parseJSON (Yaml.String nm) = pure $ AllocaName nm
  parseJSON (Yaml.Number n)
    | Just off <- toBoundedInteger n :: Maybe Word64 =
        pure $ AllocaName (Text.pack (show off))
  parseJSON v =
    fail $ "Allocation name Expected integer or string, not " ++ show v

-- | Annotes an event at a given address.
data AllocaInfo = AllocaInfo
  { allocaName :: !AllocaName
    -- ^ Name of allocation.
  , allocaBinaryOffset :: !Integer
    -- ^ Number of bytes from start of alloca to offset of stack
    -- pointer in machine code.
  }
  deriving (Show)

allocaInfoFields :: FieldList
allocaInfoFields = fields ["name", "offset"]

instance Yaml.FromJSON AllocaInfo where
  parseJSON = withFixedObject "AllocaInfo" allocaInfoFields $ \v ->
    AllocaInfo
      <$> v .: "name"
      <*> v .: "offset"

------------------------------------------------------------------------
-- BlockEventType

data BlockEventInfo
   = BinaryOnlyAccess
     -- ^ The instruction at the address updates the binary
     -- stack, but does not affect LLVM memory.
   | JointStackAccess !AllocaName
     -- ^ The instructions at the address access the LLVM allocation
     -- associated with the given name.
   | HeapAccess
     -- ^ There is an access to heap memory.
  deriving (Show)

------------------------------------------------------------------------
-- BlockEvent

-- | Annotes an event at a given address.
data BlockEvent = BlockEvent
  { eventAddr :: !Integer
  , eventInfo :: !BlockEventInfo
  }
  deriving (Show)

-- | Lift of fields
blockEventFields :: FieldList
blockEventFields = fields ["addr", "type", "alloca"]

instance Yaml.FromJSON BlockEvent where
  parseJSON = withFixedObject "BlockEvent" blockEventFields $ \v -> do
    addr <- v .: "addr"
    tp <- v .: "type"
    info <-
      case (tp :: Text) of
        "binary_only_access" -> pure BinaryOnlyAccess
        "joint_stack_access" -> do
          JointStackAccess <$> v .: "alloca"
        "heap_access" -> pure HeapAccess
    pure $ BlockEvent { eventAddr = addr
                      , eventInfo = info
                      }

------------------------------------------------------------------------
-- VCGBlockInfo

-- | Our VCG supports cases where each LLVM block corresponds to a contiguous range
-- of instructions.
data VCGBlockInfo = VCGBlockInfo
  { blockLabel :: !String
    -- ^ LLVM label of block
  , blockAddr :: !Word64
    -- ^ Address of start of block in machine code
  , blockCodeSize :: !Integer
    -- ^ Number of bytes in block
  , blockHintsRSPOffset :: !Integer
    -- ^ Offset of RSP when block starts versus initial RSP for function.
  , blockAllocas :: ![AllocaInfo]
    -- ^ Maps LLVM allocations to an offset of the stack where it starts.
  , blockEvents :: ![BlockEvent]
    -- ^ Annotates events within the block.
  }
  deriving (Show, Generic)


blockInfoFields :: FieldList
blockInfoFields = fields ["label", "addr", "size", "rsp_offset", "allocas", "events"]

instance Yaml.FromJSON VCGBlockInfo where
  parseJSON = withFixedObject "block" blockInfoFields $ \v ->
    VCGBlockInfo
      <$> v .: "label"
      <*> v .: "addr"
      <*> v .: "size"
      <*> v .: "rsp_offset"
      <*> v .: "allocas"
      <*> v .: "events"

data VCGFunInfo = VCGFunInfo
  { llvmFunName    :: !String
    -- ^ LLVM function name
  , stackSize :: !Integer
    -- ^ Number of bytes in binary stack size.
  , blocks :: [VCGBlockInfo]
    -- ^ Information relating blocks
  }
  deriving (Show, Generic)

functionInfoFields :: FieldList
functionInfoFields = fields ["llvm_name", "stack_size", "blocks"]

instance Yaml.FromJSON VCGFunInfo where
  parseJSON = withFixedObject "function" functionInfoFields $ \v ->
    VCGFunInfo
      <$> v .: "llvm_name"
      <*> v .: "stack_size"
      <*> v .: "blocks"

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
