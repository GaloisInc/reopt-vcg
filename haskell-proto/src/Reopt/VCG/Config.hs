{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Reopt.VCG.Config
  ( MetaVCGConfig(..)
  , FunctionAnn(..)
  , BlockAnn(..)
  , AllocaInfo(..)
  , AllocaName(..)
  , BlockEvent(..)
  , BlockEventInfo(..)
  ) where

import qualified Data.HashMap.Strict as HMap
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HSet
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Scientific (toBoundedInteger)
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Data.Aeson.Types as Aeson
import           Data.Aeson.Types ((.:), (.:?), (.!=))
import           GHC.Generics
import           GHC.Natural

------------------------------------------------------------------------
-- JSON utilities

-- | A list of valid fields for an object.
type FieldList = HashSet Text

-- | Create a field list from a list
fields :: [Text] -> FieldList
fields = HSet.fromList

-- | Parse a YAML and fail if there are any fields not in the set.
withFixedObject :: String
                -> FieldList
                -> (Aeson.Object -> Aeson.Parser a)
                -> Aeson.Value
                -> Aeson.Parser a
withFixedObject nm flds f (Aeson.Object o) =
  case HMap.foldrWithKey badFields [] o of
    [] -> f o
    l -> fail $ "Unexpected fields in " ++ nm ++ ": " ++ show l
  where badFields :: Text -> Aeson.Value -> [Text] -> [Text]
        badFields fld _ l =
          if HSet.member fld flds then
            l
           else
            fld:l
withFixedObject _ _ _ _ = fail "Expected an object."

------------------------------------------------------------------------
-- AllocaInfo

-- | Identifier associated with an LLVM allocation.
newtype AllocaName = AllocaName { allocaNameText :: Text }
  deriving (Eq, Ord)

instance IsString AllocaName where
  fromString = AllocaName . Text.pack

instance Show AllocaName where
  show (AllocaName nm) = Text.unpack nm

instance Aeson.FromJSON AllocaName where
  parseJSON (Aeson.String nm) = pure $ AllocaName nm
  parseJSON (Aeson.Number n)
    | Just off <- toBoundedInteger n :: Maybe Word64 =
        pure $ AllocaName (Text.pack (show off))
  parseJSON v =
    fail $ "Allocation name Expected integer or string, not " ++ show v

-- | Annotes an event at a given address.
data AllocaInfo = AllocaInfo
  { allocaName :: !AllocaName
    -- ^ Name of allocation.
  , allocaBinaryOffset :: !Natural
    -- ^ Number of bytes from start of alloca to offset of stack
    -- pointer in machine code.
  , allocaInThisBlock :: !Bool
    -- ^ Stores true if the allocation is made in this block.
  }
  deriving (Show)

allocaInfoFields :: FieldList
allocaInfoFields = fields ["name", "offset", "new"]

instance Aeson.FromJSON AllocaInfo where
  parseJSON = withFixedObject "AllocaInfo" allocaInfoFields $ \v -> do
    nm <- v .: "name"
    o <- v .: "offset"
    new <- v .: "new" .!= False
    pure AllocaInfo { allocaName = nm
                    , allocaBinaryOffset = o
                    , allocaInThisBlock = new
                    }

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

type MCAddr = Word64


-- | Annotes an event at a given address.
data BlockEvent = BlockEvent
  { eventAddr :: !MCAddr
  , eventInfo :: !BlockEventInfo
  }
  deriving (Show)

-- | Lift of fields
blockEventFields :: FieldList
blockEventFields = fields ["addr", "type", "alloca"]

instance Aeson.FromJSON BlockEvent where
  parseJSON = withFixedObject "BlockEvent" blockEventFields $ \v -> do
    addr <- v .: "addr"
    tp <- v .: "type"
    info <-
      case (tp :: Text) of
        "binary_only_access" -> pure BinaryOnlyAccess
        "joint_stack_access" -> do
          JointStackAccess <$> v .: "alloca"
        "heap_access" -> pure HeapAccess
        _ -> fail "Unexpected alloca type"
    pure $ BlockEvent { eventAddr = addr
                      , eventInfo = info
                      }

------------------------------------------------------------------------
-- BlockAnn

-- | Our VCG supports cases where each LLVM block corresponds to a contiguous range
-- of instructions.
data BlockAnn = BlockAnn
  { blockLabel :: !String
    -- ^ LLVM label of block
  , blockAddr :: !MCAddr
    -- ^ Address of start of block in machine code
  , blockCodeSize :: !Integer
    -- ^ Number of bytes in block
  , blockRSPOffset :: !Integer
    -- ^ Offset of RSP when block starts versus initial RSP for function.
    -- Since the stack grows down, this will typically be non-positive.
  , blockX87Top  :: !Int
    -- ^ The top of x87 stack (empty = 7, full = 0)
  , blockDFFlag  :: !Bool
    -- ^ The value of the DF flag (default = FalsE)
  , blockAllocas :: ![AllocaInfo]
    -- ^ Maps LLVM allocations to an offset of the stack where it starts.
  , blockEvents :: ![BlockEvent]
    -- ^ Annotates events within the block.
  }
  deriving (Show, Generic)


blockInfoFields :: FieldList
blockInfoFields = fields ["label", "addr", "size", "rsp_offset", "allocas", "events"]

instance Aeson.FromJSON BlockAnn where
  parseJSON = withFixedObject "block" blockInfoFields $ \v -> do
    lbl  <- v .: "label"
    addr <- v .: "addr"
    sz   <- v .: "size"
    rspOff  <- v .:? "rsp_offset" .!= 0
    x87Top  <- v .:? "x87_top"    .!= 7
    dfFlag  <- v .:? "df_flag"    .!= False
    allocas <- v .:? "allocas"    .!= []
    events  <- v .:? "events"     .!= []
    pure BlockAnn { blockLabel = lbl
                  , blockAddr  = addr
                  , blockCodeSize = sz
                  , blockRSPOffset = rspOff
                  , blockX87Top    = x87Top
                  , blockDFFlag    = dfFlag
                  , blockAllocas = allocas
                  , blockEvents = events
                  }

data FunctionAnn = FunctionAnn
  { llvmFunName    :: !String
    -- ^ LLVM function name
  , stackSize :: !Integer
    -- ^ Number of bytes in binary stack size.
  , blocks :: !(Map String BlockAnn)
    -- ^ Maps LLVM labels to the block associated with that label.
  }
  deriving (Show)

functionInfoFields :: FieldList
functionInfoFields = fields ["llvm_name", "stack_size", "blocks"]

instance Aeson.FromJSON FunctionAnn where
  parseJSON = withFixedObject "function" functionInfoFields $ \v -> do
    fnm <- v .: "llvm_name"
    sz  <- v .: "stack_size"
    bl <- v .: "blocks"
    pure $! FunctionAnn { llvmFunName = fnm
                        , stackSize = sz
                        , blocks = Map.fromList [ (blockLabel b, b) | b <- bl ]
                        }

data MetaVCGConfig = MetaVCGConfig
  { llvmBCFilePath :: FilePath
    -- ^ LLVM .bc file path
  , binFilePath    ::  String
    -- ^ Binary file path that will be analyzed by Macaw
  , functions :: [FunctionAnn]
  }
  deriving (Show, Generic)

instance Aeson.FromJSON MetaVCGConfig
