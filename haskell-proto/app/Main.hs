{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import           Control.Concurrent
import           Control.Exception
import           Control.Lens
import           Control.Monad
import           Control.Monad (forM_)
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ElfEdit as Elf
import           Data.IORef
import           Data.List as List
import           Data.Macaw.CFG
import           Data.Macaw.Memory.ElfLoader
import qualified Data.Macaw.Types as M
import           Data.Macaw.X86
import           Data.Macaw.X86.X86Reg
import           Data.Map (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as LText
import           Data.Parameterized.TraversableF
import           Data.Word
import qualified Data.Yaml as Yaml
import           GHC.Natural
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import qualified Text.LLVM as L
import           Text.LLVM hiding (comment, (:>), Value, LayoutSpec(..))
import           Text.Printf
import qualified What4.Protocol.SMTLib2.Parse as SMTP
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import qualified Reopt.VCG.Config as Ann
import           VCGCommon
import qualified VCGLLVM as L
import qualified VCGMacaw as M

$(pure [])

warning :: String -> IO ()
warning msg = do
  hPutStrLn stderr ("Warning: " ++ msg)

fatalError :: String -> IO a
fatalError msg = do
  hPutStrLn stderr msg
  exitFailure

$(pure [])

ppBlock :: BlockLabel -> String
ppBlock (Named (Ident s)) = s
ppBlock (Anon i) = show i

$(pure [])

-- | Find a block with the given label in the config.
findBlock :: Ann.FunctionAnn -> BlockLabel -> Maybe Ann.BlockAnn
findBlock cfg lbl = Map.lookup (ppBlock lbl) (Ann.blocks cfg)

$(pure [])

------------------------------------------------------------------------
-- ModuleVCG

-- | Information needed for checking equivalence of entire module
data ModuleVCGContext = ModuleVCGContext { moduleMem :: !(Memory 64)
                                           -- ^ Machine code memory
                                         , symbolAddrMap :: !(Map BS.ByteString (MemSegmentOff 64))
                                           -- ^ Maps bytes to the symbol name
                                         }

$(pure [])

-- | A monad for running verification of an entire module
newtype ModuleVCG a = ModuleVCG { _unModuleVCG :: ReaderT ModuleVCGContext IO a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadIO
           , MonadReader ModuleVCGContext
           )

runModuleVCG :: ModuleVCGContext -> ModuleVCG () -> IO ()
runModuleVCG ctx (ModuleVCG m) = do
  r <- runReaderT m ctx
  pure r

$(pure [])

------------------------------------------------------------------------
-- BlockVCG

-- | Callback functions for interacting with SMT solver.
--
-- These are generated separately for each block.
data CallbackFns = CallbackFns
  { addCommandCallback :: !(SMT.Command -> IO ())
    -- ^ Invoked to add an SMT command.
    --
    -- These commands must not change the solver out of assert mode.
  , proveFalseCallback :: !(SMT.Term -> String -> IO ())
    -- ^ Invoked when we have a proposition to prove is false for all
    -- interprettions.
    --
    -- The message is provide so the user knows the source of the
    -- check.
  , proveTrueCallback  :: !(SMT.Term -> String -> IO ())
    -- ^ Invoked when we have a proposition to prove is true for all
    -- interpretations.
    --
    -- The message is provide so the user knows the source of the
    -- check.
  }

$(pure [])

-- | Information that does not change during execution of @BlockVCG@.
data BlockVCGContext = BlockVCGContext
  { curFunAnnotations :: !Ann.FunctionAnn
    -- ^ Annotations for the current function we are verifying.
  , addrEventMap :: !(Map (MemSegmentOff 64) Ann.BlockEventInfo)
    -- ^ Maps address of instruction to information about memory
    -- reads/writes at that address.
  , callbackFns :: !CallbackFns
    -- ^ Functions for interacting with SMT solver.
  , mcModuleVCGContext :: !ModuleVCGContext
    -- ^ Information about machine code module.
  , mcBlockEndAddr :: !(MemAddr 64)
    -- ^ The end address of the block.
  , mcBlockMap :: !(Map (MemSegmentOff 64) Ann.BlockEventInfo)
    -- ^ Map from addresses to annotations of events on that address.
  }

$(pure [])

-- | State that changes during execution of @BlockVCG@.
data BlockVCGState = BlockVCGState
  { mcCurAddr :: !(MemSegmentOff 64)
    -- ^ Address of the current instruction
  , mcCurSize :: !(MemWord 64)
    -- ^ Size of current instruction.
  , mcX87Top :: !Int
    -- ^ Top index in x86 stack (starts at 7 and grows down).
  , mcDF :: !Bool
    -- ^ Direction flag
  , mcCurRegs :: !(RegState X86Reg (Const SMT.Term))
    -- ^ Map registers to the SMT term.
  , mcMemIndex :: !Integer
    -- ^ Index to give to next memory index
  , mcUsedAllocas :: !(Set Ann.AllocaName)
    -- ^ Map names used for allocations to @(b,e)@ where @[b,e)@
    -- represents the hardware range for addresses in the binary.
  , mcOnlyStackFrameIndex :: !Integer
    -- ^ Next index to give to `onThisFunStack` to reference predicate
    -- that a variable is on the stack frame.
  , mcEvents :: ![M.Event]
    -- ^ Unprocessed events from last instruction.
  , mcLocalIndex :: !Integer
    -- ^ Index of next local variable for machine code.
  , mcPendingAllocaOffsetMap :: !(Map Ann.AllocaName Integer)
    -- ^ This is a map from allocation names to the offset from the
    -- value in the machine code register `rsp`.  These are allocas
    -- that have not been made when the block starts.
    --
    -- The RSP is relative to the value of RSP when the machine code
    -- for the current block starts execution.
  }

$(pure [])

-- | A Monad for verifying an individual block.
newtype BlockVCG a = BlockVCG { unBlockVCG :: BlockVCGContext
                                           -> (a -> BlockVCGState -> IO ())
                                           -> BlockVCGState
                                           -> IO () }

$(pure [])

instance Functor BlockVCG where
  fmap f (BlockVCG g) = BlockVCG (\ctx c -> g ctx (c . f))

instance Applicative BlockVCG where
  pure x = seq x $ BlockVCG $ \_ c s -> c x s
  BlockVCG mf <*> BlockVCG mx = BlockVCG $ \ctx c s0 -> do
    mf ctx (\f s1 -> mx ctx (\x s2 -> let y = f x in seq y $ c y s2) s1) s0

instance Monad BlockVCG where
  BlockVCG m >>= h = BlockVCG $ \ctx c s0 -> m ctx (\a s1 -> unBlockVCG (h a) ctx c s1) s0

instance MonadReader BlockVCGContext BlockVCG where
  ask = BlockVCG $ \ctx c s -> c ctx s
  local f (BlockVCG m) =
    BlockVCG $ \ctx c s ->
                 let ctx' = f ctx
                  in seq ctx' $ m ctx' c s

instance MonadState BlockVCGState BlockVCG where
  get = BlockVCG $ \_ c s -> c s s
  put t = seq t $ BlockVCG $ \_ c _ -> c () t

instance MonadIO BlockVCG where
  liftIO m = BlockVCG $ \_ctx c s -> m >>= \a -> c a s

$(pure [])

-- | Report an error at the given location and stop verification of this block.
errorAt :: String -> BlockVCG a
errorAt msg = BlockVCG $ \_ _ s -> do
  let addr = mcCurAddr s
  hPutStrLn stderr $ "At " ++ showsPrec 10 addr ": " ++ msg

$(pure [])

addCommand :: SMT.Command -> BlockVCG ()
addCommand cmd = do
  fns <- asks callbackFns
  liftIO $ addCommandCallback fns cmd

$(pure [])

-- | @proveFalse p msg@ adds a proof obligation @p@ is false for all
-- interpretations of constants with the message @msg@.
proveFalse :: SMT.Term -> String -> BlockVCG ()
proveFalse p msg = do
  fns <- asks callbackFns
  liftIO $ proveFalseCallback fns p msg

-- | @proveTrue p msg@ adds a proof obligation @p@ is true for all
-- interpretations of constants with the message @msg@.
proveTrue :: SMT.Term -> String -> BlockVCG ()
proveTrue p msg = do
  fns <- asks callbackFns
  liftIO $ proveTrueCallback fns p msg

-- | @assertEq x y msg@ add a proof obligation named @msg@ asserting
-- that @x@ equals @y@.
assertEq :: SMT.Term -> SMT.Term -> String -> BlockVCG ()
assertEq x y msg = proveFalse (SMT.distinct [x,y]) msg

-- | Assume the propositon is true without requiring it to be proven.
assume :: SMT.Term -> BlockVCG ()
assume p = addCommand $ SMT.assert p

-- | Use a map from symbol names to address to find address.
getMCAddrOfLLVMFunction:: Map BS.ByteString (MemSegmentOff 64)
                          -- ^ Map from symbol names in machine code
                          -- to the address in the binary.
                       -> String
                       -> Either String (MemWord 64)
getMCAddrOfLLVMFunction m nm = do
  let llvmFun = UTF8.fromString nm
  case Map.lookup llvmFun m of
    Nothing -> Left $ "Cannot find address of LLVM symbol: " ++ nm
    Just expectedAddr ->
      case segoffAsAbsoluteAddr expectedAddr of
        Just addr -> pure addr
        Nothing -> Left $ "Could not resolve concrete address for " ++ nm

-- | Assert that the functions identified by the LLVM and macaw
-- function pointers are equivalent.
assertFnNameEq :: L.Symbol -> SMT.Term -> BlockVCG ()
assertFnNameEq (L.Symbol nm) macawIP = do
  -- Get the map from symbol names to the associated address
  addrMap <- asks $ symbolAddrMap . mcModuleVCGContext
  -- Get the address in the original binary of the executable.
  let Right addr = getMCAddrOfLLVMFunction addrMap nm
  -- Generate an SMT term with the address associated with the symbol.
  let expectedAddrTerm = SMT.bvhexadecimal (toInteger addr) 64
  -- Assert the two addresses are equal.
  assertEq expectedAddrTerm macawIP ("Equivalence of function: " ++ nm)

x86ArgRegs :: [X86Reg (M.BVType 64)]
x86ArgRegs = [ RDI, RSI, RDX, RCX, R8, R9 ]

-- | Information about a supported memory type.
data SupportedMemType = SupportedMemType { supportedSuffix :: !String
                                         , supportedSort :: !SMT.Sort
                                         , supportedReadDecl  :: !SMT.Command
                                         , supportedWriteDecl :: !SMT.Command
                                         }

-- | A pair containing a memrepr and the operations needed to support it in VCG.
type SupportedMemPair = (Some MemRepr, SupportedMemType)


$(pure [])

-- | Read a number of bytes as a bitvector.
-- Note. This refers repeatedly to ptr so, it should be a constant.
readBVLE :: SMT.Term -- ^ Memory
         -> SMT.Term  -- ^ Address to read
         -> Natural -- ^ Number of bytes to read.
         -> SMT.Term
readBVLE mem ptr0 w = go (w-1)
  where go :: Natural -> SMT.Term
        go 0 = SMT.select mem ptr0
        go i =
          let ptr = SMT.bvadd ptr0 [SMT.bvdecimal (toInteger i) 64]
           in SMT.concat (SMT.select mem ptr) (go (i-1))

-- | Create mem write declaration given number of bytes to write
memReadDeclBV :: Natural
              -> SMT.Command
memReadDeclBV w = do
  let nm = "mem_readbv" <> fromString (show (8*w))
  let args = [("m", memSort), ("a", ptrSort)]
  let resSort = SMT.bvSort (8*w)
  SMT.defineFun nm args resSort (readBVLE (varTerm "m") (varTerm "a") w)

$(pure [])

-- | @MacawRead addr cnt var@ reads @cnt@ bytes from machine code
-- memory and assigns them to @var@.
macawRead :: Var -> SMT.Term -> SupportedMemType -> BlockVCG ()
macawRead valVar addr supType = do
  let suf = supportedSuffix supType
  let valSort = supportedSort supType
  idx <- gets mcMemIndex
  let mem = varTerm (M.memVar idx)
  let val = SMT.term_app ("mem_read" <> fromString suf) [mem, addr]
  addCommand $ SMT.defineFun valVar [] valSort val

$(pure [])

-- | Create mem write declaration given number of bytes to write
memWriteDeclBV :: Natural -> SMT.Command
memWriteDeclBV w = do
  let nm = "mem_writebv" <> fromString (show (8*w))
  let argTypes = [("m", memSort), ("a", ptrSort), ("v", SMT.bvSort (8*w))]
  SMT.defineFun nm argTypes memSort (writeBVLE (varTerm "m") (varTerm "a") (varTerm "v") w)

$(pure [])

-- Construct a known mem pair for a nat.
supportedBV :: (1 <= w) => NatRepr w -> SupportedMemPair
supportedBV w =
  ( Some (BVMemRepr w LittleEndian)
  , let n = natValue w
     in SupportedMemType { supportedSuffix = "bv" <> show (8*n)
                         , supportedSort = SMT.bvSort (8*n)
                         , supportedReadDecl = memReadDeclBV n
                         , supportedWriteDecl = memWriteDeclBV n
                         }
  )

$(pure [])

-- | Types that may appear in reads/writes.
supportedMemTypes :: Map (Some MemRepr) SupportedMemType
supportedMemTypes = Map.fromList $
  [ supportedBV (knownNat @1)
  , supportedBV (knownNat @2)
  , supportedBV (knownNat @4)
  , supportedBV (knownNat @8)
  ]

$(pure [])

getSupportedType :: MemRepr tp -> BlockVCG SupportedMemType
getSupportedType memType =
  case Map.lookup (Some memType) supportedMemTypes of
    Nothing -> error $ "Unexpected type " ++ show memType
    Just supType -> pure supType

$(pure [])

-- | @macawWrite addr cnt val@ writes @cnt@ bytes to memory.
--
-- The value written is the @8*cnt@-length bitvector term @val@.
macawWrite :: SMT.Term -> MemRepr tp -> SMT.Term -> BlockVCG ()
macawWrite addr memType val = do
  supType <- getSupportedType memType
  idx <- gets mcMemIndex
  modify' $ \s -> s { mcMemIndex = mcMemIndex s + 1 }
  let mem = varTerm (M.memVar idx)
  let suf = supportedSuffix supType
  let newMem = SMT.term_app ("mem_write" <> fromString suf) [mem, addr, val]
  addCommand $ SMT.defineFun (M.memVar (idx+1)) [] memSort newMem

$(pure [])

comment :: Builder -> SMT.Command
comment r = SMT.Cmd $ "; " <> r

initRSP :: SMT.Term
initRSP = varTerm (M.smtRegVar RSP)

-- | Name of SMT predicate that holds if all the bytes [addr, addr+sz)` are
-- in a region of the stack frame marked as only accessible to the binary code.
--
-- Note. The correctness property above assumes that @sz > 0@.
onThisFunStack :: (Monoid a, IsString a) => Integer -> a
onThisFunStack varNum | varNum < 0 = error "onThisFunStack given negative number."
                      | otherwise = "on_mconly_stack_frame" <> fromString (show varNum)

addc :: SMT.Term -> Integer -> SMT.Term
addc t 0 = t
addc t i = SMT.bvadd t [SMT.bvdecimal i 64]

-- | @mcMemDecls sz@ adds declarations about the memory.
--
-- It assumes that there is a fresh constant x86reg_RSP declared for
-- the initial RSP, and asserts that @sz < x86reg_RSP < 2^64 - 8@
--
-- It defines @stack_low@ to be @x86reg_RSP - sz@.
-- It defines @stack_high@ to be @x86reg_RSP + 8@.
--
-- It also defines @heap_low@, @heap_high@, and @in_heap_segment@.
--
-- It defines @on_this_stack_frame@
-- Note. This assumes X86 registers are already declared.
mcMemDecls :: Integer
              -- ^ The number of bytes above initRSP available to access on stack.
           -> Integer
              -- ^ The number of bytes below initRSP available to access on stack.
           -> [SMT.Command]
mcMemDecls bytesAbove bytesBelow =
  [ -- Assert RSP has enough room to hold the return address.
    SMT.assert $ SMT.bvult initRSP (SMT.bvhexadecimal (2^(64::Int) - bytesAbove) 64)
    -- Assert RSP has enough room to hold the given number of bytes.
  , SMT.assert $ SMT.bvugt initRSP (SMT.bvdecimal bytesBelow 64)
  , comment "stack_low is the minimum address on stack."
  , SMT.defineFun "stack_low"  [] (SMT.bvSort 64)
      (SMT.bvsub initRSP (SMT.bvdecimal bytesBelow 64))
    -- High water stack pointer includes 8 bytes for return address.
  , comment "stack_high is the maxium address on stack."
  , SMT.defineFun "stack_high"  [] (SMT.bvSort 64) (addc initRSP bytesAbove)
    -- stack_high must be aligned to a 16-byte boundary.
    -- This is done by asserting the 4 low-order bits are 0.
  , SMT.assert $ SMT.eq [ SMT.extract 3 0 (varTerm "stack_high"), SMT.bvhexadecimal 0 4]
    -- Declare on_this_stack_frame
  , do let args = [("a", ptrSort), ("sz", SMT.bvSort 64)]
       SMT.defineFun (onThisFunStack 0) args SMT.boolSort $
         SMT.letBinder [ ("e", SMT.bvadd (varTerm "a") [varTerm "sz"]) ] $
           SMT.and [ SMT.bvule (varTerm "stack_low") (varTerm "a")
                   , SMT.bvule (varTerm "a") (varTerm "e")
                   , SMT.bvule (varTerm "e") (varTerm "stack_high")
                   ]
    -- Declare lower and upper bounds for heap.
  , SMT.declareConst "heap_low" (SMT.bvSort 64)
  , SMT.declareConst "heap_high" (SMT.bvSort 64)
  , SMT.assert $ SMT.bvult (varTerm "heap_low") (varTerm "heap_high")
    -- Declare in_heap_segment
  , do let args = [("a", ptrSort), ("sz", SMT.bvSort 64)]
       SMT.defineFun "in_heap_segment" args SMT.boolSort $
         SMT.letBinder [ ("e", SMT.bvadd (varTerm "a") [varTerm "sz"]) ] $
           SMT.and [ SMT.bvule (varTerm "heap_low") (varTerm "a")
                   , SMT.bvule (varTerm "a") (varTerm "e")
                   , SMT.bvule (varTerm "e") (varTerm "heap_high")
                   ]
  ]

-- | A SMT predicate that holds if all the bytes [addr, addr+sz)` is in the heap.
--
-- Note. This predicate can assume that `sz > 0` and `sz < 2^64`, but still
-- be correct if the computation of `addr+sz` overflows.
inHeapSegment :: SMT.Term -> Integer -> SMT.Term
inHeapSegment addr sz = SMT.term_app "in_heap_segment" [addr, SMT.bvdecimal sz 64]

------------------------------------------------------------------------

-- | Handler for when eventsEq doesn't match events.
handleEventMatchFailure :: [L.Event] -> M.Event -> BlockVCG ()
handleEventMatchFailure [] mev = do
  error $ "Macaw event after end of LLVM events:\n"
    ++ M.ppEvent mev
handleEventMatchFailure (lev:_) mev = do
  addr <- gets mcCurAddr
  error $ "Incompatible LLVM and Macaw events:\n"
    ++ "LLVM:  " ++ L.ppEvent lev ++ "\n"
    ++ "Macaw " ++ show addr ++ ": " ++ M.ppEvent mev

-- | When that a feature is missing.
missingFeature :: String -> BlockVCG ()
missingFeature msg = liftIO $ hPutStrLn stderr $ "TODO: " ++ msg

-- | Identifies the LLVM base address of an allocation.
allocaLLVMBaseVar :: Ann.AllocaName -> Text
allocaLLVMBaseVar (Ann.AllocaName nm) = mconcat ["alloca_", nm, "_llvm_base"]

-- | Identifies the LLVM end address of an allocation.
allocaLLVMEndVar :: Ann.AllocaName -> Text
allocaLLVMEndVar (Ann.AllocaName nm)  = mconcat ["alloca_", nm, "_llvm_end"]

-- | Identifies the machine code base address of an allocation.
allocaMCBaseVar :: Ann.AllocaName -> Text
allocaMCBaseVar (Ann.AllocaName nm) = mconcat ["alloca_", nm, "_mc_base"]

-- | Identifies the LLVM end address of an allocation.
allocaMCEndVar :: Ann.AllocaName -> Text
allocaMCEndVar (Ann.AllocaName nm)  = mconcat ["alloca_", nm, "_mc_end"]

-- | A range @(b,e)@ representing the addresses @[b..e)@.
-- We assume that @b ule e@.
type Range = (SMT.Term, SMT.Term)

-- | @isDisjoint x y@ returns a predicate that holds if the ranges denoted by @x@ and @y@
-- do not overlap.
isDisjoint :: Range -> Range -> SMT.Term
isDisjoint (b0, e0) (b1, e1) = SMT.or [ SMT.bvule e0 b1, SMT.bvule e1 b0 ]

-- | @assumeLLVMDisjoint (base, end) nm@ adds assumptions that @[base,end)@
-- is disjoint from allocation identified by @nm@.
--
-- We can assume @end >= base@ for all allocations
assumeLLVMDisjoint :: Range -> Ann.AllocaName -> BlockVCG ()
assumeLLVMDisjoint r nm = do
  assume $ isDisjoint r (varTerm (allocaLLVMBaseVar nm), varTerm (allocaLLVMEndVar nm))

-- | Check if LLVM type and Macaw types are compatible.
typeCompat :: L.Type -> MemRepr tp -> Bool
typeCompat (L.PrimType (L.Integer lw)) (BVMemRepr mw _) =
  toInteger lw == 8 * intValue mw
typeCompat (L.PtrTo _tp) (BVMemRepr mw _) =
  intValue mw == 64
typeCompat (L.PrimType (L.FloatType L.Float)) (FloatMemRepr SingleFloatRepr _) =
  True
typeCompat (L.PrimType (L.FloatType L.Double)) (FloatMemRepr DoubleFloatRepr _) =
  True
typeCompat (L.PrimType (L.FloatType L.X86_fp80)) (FloatMemRepr X86_80FloatRepr _) =
  True
typeCompat (L.Vector ln ltp) (PackedVecMemRepr mn mtp) =
  toInteger ln == intValue mn && typeCompat ltp mtp
typeCompat _ _ = False

processMCEvents :: [M.Event] -> BlockVCG [M.Event]
processMCEvents (M.CmdEvent cmd:mevs) = do
  addCommand cmd
  processMCEvents mevs
processMCEvents (M.WarningEvent msg:mevs) = do
  liftIO $ hPutStrLn stderr msg
  processMCEvents mevs
processMCEvents (M.InstructionEvent _curAddr:mevs) = do
  processMCEvents mevs
processMCEvents (M.MCOnlyStackReadEvent mcAddr tp macawValVar:mevs) = do
  -- Assert address is on stack
  do addr <- gets mcCurAddr
     idx <- gets mcOnlyStackFrameIndex
     let sz = memReprBytes tp
     proveTrue (SMT.term_app (onThisFunStack idx) [mcAddr, SMT.bvdecimal sz 64])
               (printf "Machine code read at %s is in unreserved stack space." (show addr))
  -- Define value from reading Macaw heap
  supType <- getSupportedType tp
  macawRead macawValVar mcAddr supType
  -- Process future events.
  processMCEvents mevs
-- Every LLVM write should have a machine code write (but not
-- necessarily vice versa), we first pattern match on machine code
-- writes.
processMCEvents (M.MCOnlyStackWriteEvent mcAddr tp macawVal:mevs) = do
  -- Update stack with write.
  macawWrite mcAddr tp macawVal
  -- Assert address is on stack
  do addr <- gets mcCurAddr
     idx <- gets mcOnlyStackFrameIndex
     let sz = memReprBytes tp
     proveTrue (SMT.term_app (onThisFunStack idx) [mcAddr, SMT.bvdecimal sz 64])
               (printf "Machine code write at %s is in unreserved stack space." (show addr))
  -- Process next events
  processMCEvents mevs
-- Fallback case
processMCEvents mevs = pure mevs

-- | Return true if the first address is always less than second.
addrLt :: MemAddr 64 -> MemAddr 64 -> Bool
addrLt x y = addrBase x == addrBase y && addrOffset x < addrOffset y

mcNextAddr :: BlockVCGState -> MemAddr 64
mcNextAddr s = incAddr (toInteger (mcCurSize s)) (segoffAddr (mcCurAddr s))


getNextEvents :: BlockVCG ()
getNextEvents = do
  ctx <- ask
  s <- get
  let addr = mcNextAddr s
  if not (addrLt addr (mcBlockEndAddr ctx)) then
    error $ "Unexpected end of machine code events."
   else do
    let mem = moduleMem (mcModuleVCGContext ctx)
    let Just addrSegOff = asSegmentOff mem addr
    let loc = ExploreLoc { loc_ip = addrSegOff
                         , loc_x87_top = mcX87Top s
                         , loc_df_flag = mcDF s
                         }
    let (r, nextIdx, sz) =
           M.blockEvents (mcBlockMap ctx) (mcCurRegs s) (mcLocalIndex s) loc
    -- Update local index and next addr
    put $! s { mcLocalIndex = nextIdx
             , mcCurAddr  = addrSegOff
             , mcCurSize  = sz
             }
    -- Process events
    evts <- processMCEvents r
    -- Update events
    modify $ \t -> t { mcEvents = evts }

popMCEvent :: BlockVCG M.Event
popMCEvent = do
  evts0 <- gets mcEvents
  ctx <- ask
  nextAddr <- gets mcNextAddr
  case evts0 of
    [] -> do
      getNextEvents
      popMCEvent
    -- This checks to see if the next instruction jumps to the next ip,
    -- and if so it runs it.
    (M.FetchAndExecuteEvent ectx regs:r)
      -- Check IP in registers matches next register
      | Just ipAddr <- valueAsMemAddr (regs^.boundValue X86_IP)
      , nextAddr == ipAddr
      , addrLt ipAddr (mcBlockEndAddr ctx) -> do
      when (not (null r)) $ do
        error "MC event after fetch and execute"
      modify $ \s -> s { mcEvents = [] }
      -- Update loc_x86_top and loc_df_flag
      case regs^.boundValue X87_TopReg of
        BVValue _w i | 0 <= i, i <= 7 -> do
          modify $ \s -> s { mcX87Top = fromInteger i }
        _ -> error "Unexpected X87_TOP value"
      case regs^.boundValue DF of
        BoolValue b ->
          modify $ \s -> s { mcDF = b }
        _ -> error "Unexpected direction flag"
      -- Update registers
      modify $ \s -> s { mcCurRegs = fmapF (Const . M.primEval ectx) regs }
      -- Process next events
      getNextEvents
      popMCEvent
    (h:r) -> do
      evts <- processMCEvents r
      modify $ \s -> s { mcEvents = evts }
      pure h

popFetchAndExecute :: BlockVCG (RegState (ArchReg X86_64) (Const SMT.Term))
popFetchAndExecute = do
  evt <- popMCEvent
  case evt of
    M.FetchAndExecuteEvent ectx regs -> do
      r <- gets mcEvents
      when (not (null r)) $ do
        error "MC event after fetch and execute"
      pure $! fmapF (Const . M.primEval ectx) regs
    _ -> do
      error "Missing fetch and execute event."

{-
-- | Check that we are at end of MC events
checkReachedMCEventEnd :: BlockVCG ()
checkReachedMCEventEnd = do
  mevents <- gets mcEvents
  mevents' <- processMCEvents mevents
  case mevents' of
    [] -> do
      modify $ \s -> s { mcEvents = [] }
    mev:_ -> do
      error $ "Macaw event after end of LLVM events:\n" ++ M.ppEvent mev
-}

-- | Process LLVM and macaw events to ensure they are equivalent.
eventsEq :: [L.Event]
         -> BlockVCG ()
eventsEq (L.CmdEvent cmd:levs) = do
  addCommand cmd
  eventsEq levs
eventsEq (L.AllocaEvent (Ident nm0) sz _align:levs) = do
  let  nm = Ann.AllocaName (Text.pack nm0)
  -- Define base of alloca
  addCommand $ SMT.declareConst (allocaLLVMBaseVar nm) ptrSort
  let llvmBase = varTerm (allocaLLVMBaseVar nm)
  -- Define register alloca is returned to.
  addCommand $ SMT.defineFun ("llvm_" <> Ann.allocaNameText nm) [] ptrSort llvmBase
  -- Define end of alloca
  addCommand $ SMT.defineFun (allocaLLVMEndVar nm) [] ptrSort $ SMT.bvadd llvmBase [sz]
  let llvmEnd = varTerm (allocaLLVMEndVar nm)
  -- Assert end calculation did not wrap around.
  assume $ SMT.bvule llvmBase llvmEnd
  -- Get machine code offset.

  -- Get pending allocations
  allocaMap <- gets $ mcPendingAllocaOffsetMap
  -- Lookup offset of this allocation in pending allocations
  mcOffset <-
    case Map.lookup nm allocaMap of
      Nothing ->
        error $ "Could not find offset of alloca with name: " ++ show nm ++ "\n" ++ "Names: " ++ show (Map.keys allocaMap)
      Just o -> pure o

  -- Delete this from pending allocations
  modify $ \s -> s { mcPendingAllocaOffsetMap = Map.delete nm allocaMap }

  -- get machine code base address of allocation.
  let mcAddr | mcOffset >= 0 = SMT.bvadd initRSP [SMT.bvdecimal mcOffset 64]
             | otherwise =  SMT.bvsub initRSP (SMT.bvdecimal (negate mcOffset) 64)

  -- Validate mcOffset is less than stack higher
  -- Define machine code base
  addCommand $ SMT.defineFun (allocaMCBaseVar nm) [] ptrSort mcAddr

  let mcAllocBase = varTerm (allocaMCBaseVar nm)

  addCommand $ SMT.defineFun (allocaMCEndVar nm) [] ptrSort $
    SMT.bvadd mcAllocBase [sz]
  let mcAllocEnd = varTerm (allocaMCEndVar nm)

  -- Check stack space is unallocated
  do idx <- gets mcOnlyStackFrameIndex
     proveTrue (SMT.term_app (onThisFunStack idx) [mcAllocBase, sz])
       (printf "Machine code space for %s in unreserved stack space." (show nm))
  -- Update region of unallocated stack space.
  do idx <- gets mcOnlyStackFrameIndex
     modify $ \s -> s { mcOnlyStackFrameIndex = idx + 1 }
     let args = [("a", ptrSort), ("sz", SMT.bvSort 64)]
     addCommand $ SMT.defineFun (onThisFunStack (idx+1)) args SMT.boolSort $
       let e = SMT.bvadd (varTerm "a") [varTerm "sz"]
        in SMT.and [ isDisjoint (varTerm "a", e) (mcAllocBase, mcAllocEnd)
                   , SMT.term_app (onThisFunStack idx) [varTerm "a", varTerm "sz"]
                   ]
  -- Adding assumptions about non-overlap.
  do used <- gets mcUsedAllocas
     when (Set.member nm used) $ error $ show nm ++ " is already used an allocation."
     mapM_ (assumeLLVMDisjoint (llvmBase,llvmEnd)) used
     modify $ \s -> s { mcUsedAllocas = Set.insert nm (mcUsedAllocas s) }
  -- Process next events
  eventsEq levs

eventsEq levs0@(L.LoadEvent llvmLoadAddr llvmType llvmValVar:levs) = do
  mevt <- popMCEvent
  case mevt of
    M.JointStackReadEvent mcAddr mcType macawValVar aname -> do
      -- Check size of writes are equivalent.
      unless (typeCompat llvmType mcType) $ do
        error "Incompatible LLVM and machine code types."
      let sz = memReprBytes mcType
      -- Check alloca is defined
      do used <- gets $ mcUsedAllocas
         when (not (Set.member aname used)) $ error $ "Unknown alloca: " ++ show aname
      -- Assert LLVM address is within @allocaName@
      let llvmAllocBase = varTerm $ allocaLLVMBaseVar aname
      let llvmAllocEnd  = varTerm $ allocaLLVMEndVar  aname
      let mcBase   = varTerm $ allocaMCBaseVar   aname
      let llvmLoadEnd = SMT.bvadd llvmLoadAddr [SMT.bvdecimal sz 64]
      proveTrue (SMT.bvult llvmLoadAddr (SMT.bvhexadecimal (negate sz) 64))
        ("LLVM load address does not overflow")
      proveTrue (SMT.and [ SMT.bvule llvmLoadAddr llvmAllocBase
                         , SMT.bvule llvmLoadEnd  llvmAllocEnd
                         ])
        (printf "LLVM load address is within allocation %s" (show aname))
      -- Assert machine code address is same offset of machine code region as LLVM address.
      assertEq mcAddr (SMT.bvadd mcBase [SMT.bvsub llvmLoadAddr llvmAllocBase])
        ("Machine code stack load address matches expected from LLVM")
      -- Define value from reading Macaw heap
      supType <- getSupportedType mcType
      macawRead macawValVar mcAddr supType
      let smtType = supportedSort supType
      -- Define LLVM value
      addCommand $ SMT.defineFun llvmValVar [] smtType (varTerm macawValVar)
      -- Process future events.
      eventsEq levs
    M.HeapReadEvent mcAddr mcType macawValVar -> do
      -- Assert addresses are the same
      assertEq mcAddr llvmLoadAddr
        ("Machine code heap load address matches expected from LLVM")
      -- Add that macaw points to the heap
      do addr <- gets mcCurAddr
         proveTrue (inHeapSegment mcAddr (memReprBytes mcType))
           (printf "Read from heap at %s is valid." (show addr))

      -- Check size of writes are equivalent.
      unless (typeCompat llvmType mcType) $ do
        error "Incompatible LLVM and machine code types."
      -- Define value from reading Macaw heap
      supType <- getSupportedType mcType
      macawRead macawValVar mcAddr supType
      let smtType = supportedSort supType
      -- Define LLVM value returned in terms of macaw value
      addCommand $ SMT.defineFun llvmValVar [] smtType (varTerm macawValVar)
      -- Process future events.
      eventsEq levs
    _ -> do
      handleEventMatchFailure levs0 mevt

eventsEq levs0@(L.StoreEvent llvmAddr llvmType llvmVal:levs) = do
  mevt <- popMCEvent
  case mevt of
    M.JointStackWriteEvent mcAddr mcType mcVal allocName -> do
      -- Check the number of bytes written are the same.
      unless (typeCompat llvmType mcType) $ do
        errorAt $ "Machine code and LLVM writes have incompatible types:\n"
            ++ "MC type:   " ++ show mcType ++ "\n"
            ++ "LLVM type: " ++ show llvmType

      let llvmAllocaBase :: SMT.Term
          llvmAllocaBase = varTerm ("llvm_" <> Ann.allocaNameText allocName)
      let mcAllocaBase :: SMT.Term
          mcAllocaBase = varTerm (allocaMCBaseVar allocName)
      let mcAllocaEnd :: SMT.Term
          mcAllocaEnd = varTerm (allocaMCEndVar allocName)
      -- Steps:
      -- Prove: mcAllocaBase + mcCount computation will not overflow.
      proveTrue (SMT.bvult mcAddr (SMT.bvhexadecimal (negate (memReprBytes mcType)) 64))
                "Check machine code address does not overflow."
      -- Prove: mcAllocaBase <= mcAddr
      proveTrue (SMT.bvule mcAllocaBase mcAddr)
                "Check address of machine code stack write is at allocation base or higher."
      -- Get address of end of write.
      let mcWriteEnd :: SMT.Term
          mcWriteEnd = SMT.bvadd mcAddr [SMT.bvhexadecimal (memReprBytes mcType) 64]
      -- Prove: mcWriteEnd <= allocation end
      proveTrue (SMT.bvule mcWriteEnd mcAllocaEnd)
                "Check machine code write ends before allocation end."
      -- Prove: llvmAddr - llvmAllocaBase = mcAddr - mcAllocaBase
      let llvmOffset = SMT.bvsub llvmAddr llvmAllocaBase
      let mcOffset   = SMT.bvsub   mcAddr   mcAllocaBase
      proveTrue (SMT.eq [llvmOffset, mcOffset])
                "Check we are writing to the same allocation offsets."
      -- Update macaw memory (TODO: See if we really need to do this)
      macawWrite mcAddr mcType mcVal
      -- Process future events
      eventsEq levs
    M.HeapWriteEvent mcAddr mcType macawVal -> do
      -- Check types agree.
      unless (typeCompat llvmType mcType) $ do
        error "Macaw and LLVM writes have different types."
      missingFeature "Assert machine code and llvm heap write addresses are equal."

      -- Assert values are equal
      assertEq llvmVal macawVal
        ("Machine code heap store matches expected from LLVM")
      -- Update macaw memory
      macawWrite mcAddr mcType macawVal
      -- Process future events
      eventsEq levs
    _ -> do
      handleEventMatchFailure levs0 mevt

eventsEq (L.InvokeEvent _ f lArgs lRet:levs)  = do
  regs <- popFetchAndExecute
  let Const mRegIP = regs ^. boundValue X86_IP
  assertFnNameEq f mRegIP
  -- Verify that the arguments should be same.  Note: Here we take the
  -- number of arguments from LLVM side, since the number of arguments
  -- in Macaw side seems not explicit.  Also assuming that the # of
  -- arguments of LLVM side is less or equal than six.
  when (length lArgs > length x86ArgRegs) $ do
    error $ "Too many arguments."

  missingFeature "Check return address is pushed to stack in call."

  let compareArg :: SMT.Term -> X86Reg (M.BVType 64) -> BlockVCG ()
      compareArg la reg = do
        let Const ma = regs^.boundValue reg
        assertEq la ma "Register matches LLVM"
  zipWithM_ compareArg lArgs x86ArgRegs
  -- If LLVM side has a return value, then we define the LLVM event in terms
  -- of the value bound to RAX for the rest of the program.
  case lRet of
    Just (llvmIdent, tp) -> do
      -- Returned pointers are assumed to be on heap, so we can assume they are equal.
      let Const mRetVal = regs^.boundValue RAX
      let smtSort = case tp of
                      PtrTo _ -> SMT.bvSort 64
                      PrimType (Integer 64) -> SMT.bvSort 64
                      _ ->  error $ "TODO: Add support for return type " ++ show tp
      addCommand $ SMT.defineFun (L.identVar llvmIdent) [] smtSort  mRetVal
    Nothing -> pure ()
  -- Process future events
  eventsEq levs
eventsEq [L.JumpEvent lbl]  = do
  regs <- popFetchAndExecute
  fnAnn <- asks $ curFunAnnotations
  tgtBlockAnn <-
    case findBlock fnAnn lbl of
      Just b -> pure b
      Nothing -> do
        fail $ "Could not find jump target " ++ show lbl
  -- Get term for address associated with this label.
  let llvmMemAddr = SMT.bvhexadecimal (toInteger (Ann.blockAddr tgtBlockAnn)) 64
  let Const mRegIP = regs ^. boundValue X86_IP
  assertEq llvmMemAddr mRegIP "Jump targets match"

  -- Preconditions include rsp offset delta, return address is on stack, x87Top value, dfFlag value,
  -- allocas correct, and
  missingFeature "Assert preconditions for block."
eventsEq [L.ReturnEvent mlret] = do
  regs <- popFetchAndExecute
  -- Assert the IP after the fetch and execute is the return address
  assertEq (getConst (regs^.curIP)) (varTerm "return_addr")
    "Return addresses match"

  -- Assert the stack height at the return is the peak stack height
  assertEq (getConst (regs^.boundValue RSP)) (varTerm "stack_high")
    "Stack height at return matches init"

  missingFeature "Assert callee saved registers have not changed."

  -- Assert the value in RAX is the return value.
  case mlret of
    Nothing -> pure ()
    Just lret -> do
      let Const mret = regs^.boundValue RAX
      assertEq lret mret "Return values match"
eventsEq (lev:_) = do
  error $ "Unexpected LLVM event:\n" ++ L.ppEvent lev
eventsEq [] = do
  error $ "We have reached end of LLVM events without a block terminator."
--  checkReachedMCEventEnd
--  missingFeature "Check IP has reached end of block

forceResolveAddr :: Memory w -> MemWord w -> MemSegmentOff w
forceResolveAddr mem a =
  case resolveAbsoluteAddr mem a of
    Just segOff -> segOff
    Nothing -> error $ "Could not resolve " ++ show a

-- | Analyze block events in annotations to associated each address
--with a read with the type of read (mconly stack, translated stack or heap).
extractMemEvents :: Memory 64 -> [Ann.BlockEvent] -> Map (MemSegmentOff 64) Ann.BlockEventInfo
extractMemEvents mem events = Map.fromList
  [ (forceResolveAddr mem (fromIntegral (Ann.eventAddr evt)), Ann.eventInfo evt)
  | evt <- events
  ]

-- | Read output from solver @stderr@ and print it to our @stderr@.
reportSMTErrors :: Handle -> IO ()
reportSMTErrors h = forever $ do
  msg <- hGetLine h
  hPutStrLn stderr $ "Solver: " ++ msg

-- | Kill thrad and terminate process.
cleanup :: ProcessHandle -> ThreadId -> IO ()
cleanup ph tid = do
  killThread tid
  terminateProcess ph

-- | Emit an SMT command to the solver.
writeCommand :: Handle -> SMT.Command -> IO ()
writeCommand h (SMT.Cmd b) =
  LText.hPutStrLn h (Builder.toLazyText b)

-- | Information needed for interatively verifying goal.
data InteractiveContext = InteractiveContext
  { ictxAnnFile :: !FilePath
     -- ^ Name of YAML file for error-reporting purposes
  , ictxFunName :: !String
    -- ^ Name of function to verify
  , ictxBlockLabel :: !String
     -- ^ Label of block
  , ictxAllGoalCounter :: !(IORef Integer)
    -- ^ Counter for all goals
  , ictxVerifiedGoalCounter :: !(IORef Integer)
    -- ^ Counter for all successfully verified goals.
  , ictxBlockGoalCounter :: !(IORef Integer)
    -- ^ Index of goal to discharge within block
  , ictxCmdHandle :: !Handle
     -- ^ Handle for sending commands to
  , ictxRespHandle :: !Handle
     -- ^ Handle for reading responses from
  }


-- | Function to verify a SMT proposition is unsat.
interactiveVerifyGoal :: InteractiveContext -- ^ Context for verifying goals
                      -> SMT.Term
                         -- ^ Negation of goal to verify
                      -> String
                         -- ^ Name of proposition for reporting purposes.
                      -> IO ()
interactiveVerifyGoal ictx ng propName = do
  let annFile = ictxAnnFile ictx
  let funName = ictxFunName ictx
  let lbl = ictxBlockLabel ictx
  let cmdHandle = ictxCmdHandle ictx
  let respHandle = ictxRespHandle ictx

  cnt <- readIORef (ictxBlockGoalCounter ictx)
  modifyIORef' (ictxAllGoalCounter ictx)      (+1)
  modifyIORef' (ictxVerifiedGoalCounter ictx) (+1)
  modifyIORef' (ictxBlockGoalCounter ictx)    (+1)
  let fname = standaloneGoalFilename funName lbl cnt
  hPutStrLn stderr $ "Verifying: " ++ propName
  writeCommand cmdHandle $ SMT.checkSatAssuming [ng]
  hFlush cmdHandle
  resp <- SMTP.readCheckSatResponse respHandle
  case resp of
    SMTP.SatResponse -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr ""
      hPutStrLn stderr $ printf "To see output, run `reopt-vcg %s --export <dir>`." annFile
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.UnsatResponse -> do
      hPutStrLn stdout $ "  Verified " ++ fname
    SMTP.UnknownResponse -> do
      hPutStrLn stderr $ "Unknown verification result"
      hPutStrLn stderr ""
      hPutStrLn stderr $ printf "To see output, run `reopt-vcg %s --export <dir>`." annFile
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.CheckSatUnsupported -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver does not support check-sat-assuming."
    (SMTP.CheckSatError msg) -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver returned the following message after check-sat-assuming:"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "  " ++ msg

runCallbacks :: FilePath -- ^ Name of yaml file for error reporting purposes.
             -> String -- ^ Command line for running SMT solver
             -> (CallbackGenerator -> IO a)
             -> IO a
runCallbacks annFile cmdline cont = do
  -- Counter for all goals
  allGoalCounter <- newIORef 0
  -- Counter for goals successfully verified.
  verifiedGoalCounter <- newIORef 0
  let cbg = CBG $ \funName lbl action -> do
        -- Create Goal counter for just this block.
        blockGoalCounter <- newIORef 0
        let cp = (shell cmdline)
              { std_in = CreatePipe
              , std_out = CreatePipe
              , std_err = CreatePipe
              }
        createResult <- try $ createProcess cp
        case createResult of
          Right (Just cmdHandle, Just respHandle, Just errHandle, ph) -> do
            errThread <- forkIO $ reportSMTErrors errHandle
            flip finally (cleanup ph errThread) $ do
              writeCommand cmdHandle $ SMT.setLogic SMT.allSupported
              writeCommand cmdHandle $ SMT.setProduceModels True
              let ictx = InteractiveContext { ictxAnnFile = annFile
                                            , ictxFunName = funName
                                            , ictxBlockLabel = lbl
                                            , ictxAllGoalCounter = allGoalCounter
                                            , ictxVerifiedGoalCounter = verifiedGoalCounter
                                            , ictxBlockGoalCounter = blockGoalCounter
                                            , ictxCmdHandle = cmdHandle
                                            , ictxRespHandle = respHandle
                                            }
              let fns = CallbackFns
                    { addCommandCallback = \cmd -> do
                        writeCommand cmdHandle cmd
                    , proveFalseCallback = \p msg -> do
                        interactiveVerifyGoal ictx p msg
                    , proveTrueCallback = \p msg -> do
                        interactiveVerifyGoal ictx (SMT.not p) msg
                    }
              action fns
          Right _ -> do
            hPutStrLn stderr $ "Unexpected failure running " ++ cmdline
            exitFailure
          Left err -> do
            hPutStrLn stderr $ "Could not execute " ++ cmdline
            hPutStrLn stderr $ "  " ++ show (err :: IOException)
            exitFailure
  r <- cont cbg
  do allCnt <- readIORef allGoalCounter
     verCnt <- readIORef verifiedGoalCounter
     if verCnt < allCnt then do
       hPutStrLn stdout "Verification Failed"
      else do
       hPutStrLn stdout "Verification Succeeded"
     hPutStrLn stdout $ "Verified " ++ show verCnt ++ "/" ++ show allCnt ++ " Goals."

  pure r

type FunctionName = String

-- | Tool for running verification conditions.
newtype CallbackGenerator
   = CBG { blockCallbacks :: forall a . FunctionName -> String-> (CallbackFns -> IO a) -> IO a
         }

exportCheckSatProblem :: FilePath
                         -- ^ Directory to write file to.
                      -> String -- ^ Name of function
                      -> String -- ^ Name of label of block we are generating.
                      -> IORef Integer -- ^ Index of goal to discharge within block
                      -> IORef Builder.Builder  -- ^ A representation of all commands added.
                      -> SMT.Term -- ^ Proposition to assert and check unsat of.
                      -> String   -- ^ Name of goal to prove
                      -> IO ()
exportCheckSatProblem outDir fn lbl goalCounter cmdRef negGoal msg = do
  cnt <- readIORef goalCounter
  modifyIORef' goalCounter (+1)
  cmds <- readIORef cmdRef
  let fname = standaloneGoalFilename fn lbl cnt
  hPutStrLn stdout $ fname ++ ": " ++ msg
  bracket (openFile (outDir </> fname) WriteMode) hClose $ \h -> do
    writeCommand h $ comment (fromString msg)
    writeCommand h $ SMT.setLogic SMT.allSupported
    writeCommand h $ SMT.setProduceModels True
    -- Write commands from proof state
    LText.hPutStr h (Builder.toLazyText cmds)
    writeCommand h $ SMT.checkSatAssuming [negGoal]
    writeCommand h $ SMT.exit

exportCallbacks :: FilePath
                   -- ^ Directory to write file to.
                -> String -- ^ Name of function
                -> String -- ^ Block label
                -> (CallbackFns -> IO a)
                -> IO a
exportCallbacks outDir fn lbl action = do
  goalCounter <- newIORef 0
  cmdRef <- newIORef mempty
  action $! CallbackFns
    { addCommandCallback = \(SMT.Cmd cmd) -> do
        modifyIORef' cmdRef $ \s -> s <> cmd <> "\n"
    , proveFalseCallback = \p msg ->
        exportCheckSatProblem outDir fn lbl goalCounter cmdRef p msg
    , proveTrueCallback = \p msg ->
        exportCheckSatProblem outDir fn lbl goalCounter cmdRef (SMT.not p) msg
    }

runVCGs :: CallbackGenerator
        -> Ann.FunctionAnn -- ^ Annotations for the function we are verifying.
        -> ExploreLoc -- ^ Segment offset of this block.
        -> Ann.BlockAnn -- ^ Annotations for the block we are verifying.
        -> BlockVCG ()
        -> ModuleVCG ()
runVCGs gen funAnn loc blockAnn action = do
  modCtx <- ask
  let thisSegOff = loc_ip loc
  let mem = moduleMem modCtx
  liftIO $ blockCallbacks gen (Ann.llvmFunName funAnn) (Ann.blockLabel blockAnn) $ \fns -> do
    let allocaMap = Map.fromList
          [ (Ann.allocaName a, Ann.allocaBinaryOffset a)
          | a <- Ann.blockAllocas blockAnn
          , Ann.allocaInThisBlock a
          ]
    when (any (not . Ann.allocaInThisBlock) (Ann.blockAllocas blockAnn)) $ do
      error "Do not yet support existing allocas"
    let blockStart = Ann.blockAddr blockAnn
    let sz = Ann.blockCodeSize blockAnn
    let blockEnd =
          if toInteger blockStart + sz < toInteger (maxBound :: Word64) then
            blockStart + fromInteger sz
          else
            error $ "Block overflows memory."
    let blockMap = Map.fromList
          [ (segOff, Ann.eventInfo e)
          | e <- Ann.blockEvents blockAnn
            -- Get segment offset of event.
          , let ea = Ann.eventAddr e
          , let segOff =
                  if blockStart <= ea && ea < blockEnd then
                    case incSegmentOff thisSegOff (toInteger (ea - blockStart)) of
                      Just so -> so
                      Nothing -> error "Block extends outside of starting memory segment"
                   else
                    error "Memory event annotation out of range."
          ]

    let ctx = BlockVCGContext { curFunAnnotations = funAnn
                              , addrEventMap
                                  = extractMemEvents mem
                                  $ Ann.blockEvents blockAnn
                              , callbackFns = fns
                              , mcModuleVCGContext = modCtx
                              , mcBlockEndAddr = incAddr sz (segoffAddr thisSegOff)
                              , mcBlockMap = blockMap
                              }
    let initReg :: X86Reg tp -> SMT.Term
        initReg r
          | Just Refl <- testEquality r X86_IP =
              M.evalMemAddr (segoffAddr thisSegOff)
          | Just Refl <- testEquality r X87_TopReg =
              SMT.bvdecimal (toInteger (loc_x87_top loc)) 3
          | Just Refl <- testEquality r DF         =
              if loc_df_flag loc then SMT.true else SMT.false
          | otherwise = varTerm (M.smtRegVar r)
    let s = BlockVCGState { mcCurAddr   = loc_ip loc
                          , mcCurSize   = 0
                          , mcX87Top    = loc_x87_top loc
                          , mcDF        = loc_df_flag loc
                          , mcCurRegs  = mkRegState (Const . initReg)
                          , mcMemIndex = 0
                          , mcUsedAllocas = Set.empty
                          , mcOnlyStackFrameIndex = 0
                          , mcEvents = []
                          , mcLocalIndex = 0
                          , mcPendingAllocaOffsetMap = allocaMap
                          }
    seq ctx $ seq s $ unBlockVCG action ctx (\() _ -> pure ()) s

data VerificationMode
   = DefaultMode
   | ExportMode !FilePath
   | RunSolver !String

isDefault :: VerificationMode -> Bool
isDefault DefaultMode = True
isDefault _ = False

data VCGArgs
   = VCGArgs { reoptYaml :: !(Maybe FilePath)
               -- ^ Location with yaml file.
             , requestedMode :: !VerificationMode
             }

data VCGCommand
  = ShowHelp
  | RunVCG !VCGArgs

parseArgs :: [String] -> VCGArgs -> Except String VCGCommand
parseArgs cmdArgs args = seq args $
  case cmdArgs of
    [] -> pure $! RunVCG args
    ("--help":_) -> pure $! ShowHelp
    ("--export":path:rest) -> do
      unless (isDefault (requestedMode args)) $ do
        throwError $ "Cannot specify --export or --solver multiple times."
      parseArgs rest $ args { requestedMode = ExportMode path }
    ("--solver":cmdline:rest) -> do
      unless (isDefault (requestedMode args)) $ do
        throwError $ "Cannot specify --export or --solver multiple times."
      parseArgs rest $ args { requestedMode = RunSolver cmdline }
    (path:rest) -> do
      when ("--" `isPrefixOf` path) $ do
        throwError $ "Unexpected flag " ++ path
      when (isJust (reoptYaml args)) $ do
        throwError $ "Multiple VCG files specified."
      parseArgs rest $ args { reoptYaml = Just path }

showHelp :: IO ()
showHelp = do
  putStrLn
    $  "reopt-vcg generates verification conditions to prove that reopt generated\n"
    ++ "   LLVM is faithful to the input binary.\n"
    ++ "Usage: reopt-vcg <input.yaml> {--export <export-dir> | --solver <solver-path>}"

showError :: String -> IO a
showError msg = do
  hPutStrLn stderr $ "Error: " ++ msg
  hPutStrLn stderr $ "Run `reopt-vcg --help` for additional information."
  exitFailure

withVCGArgs :: (Ann.MetaVCGConfig -> CallbackGenerator -> IO a) -> IO a
withVCGArgs action = do
  cmdArgs <- getArgs
  let initVCG = VCGArgs { reoptYaml = Nothing, requestedMode = DefaultMode }
  args <-
    case runExcept (parseArgs cmdArgs initVCG) of
      Left msg ->
        showError msg
      Right ShowHelp -> do
        showHelp
        exitSuccess
      Right (RunVCG a) -> pure a

  -- Get path to YAML
  annFile <-
    case reoptYaml args of
      Nothing -> showError "Missing VCG file to run."
      Just path -> return path
  cfg <- do
    vcgResult <- Yaml.decodeFileWithWarnings annFile
    case vcgResult of
      Left err -> do
        hPutStrLn stderr $ "Error parsing Yaml: " ++ show err
        exitFailure
      Right (warnings, cfg) -> do
        when (not (null warnings)) $ do
          hPutStrLn stderr $ "Warnings when parsing Yaml file:"
          forM_ warnings $ \warn -> do
            hPutStrLn stderr $ "  " ++ show warn
          exitFailure
        pure cfg
  case requestedMode args of
    ExportMode outdir -> do
      r <- try $ createDirectoryIfMissing True outdir
      case r of
        Right () -> do
          putStrLn $ "Writing output to " ++ outdir
          action cfg $ CBG $ exportCallbacks outdir
        Left e -> do
          hPutStrLn stderr $ "Error creating output directory: " ++ outdir
          hPutStrLn stderr $ "  " ++ show (e :: IOError)
          exitFailure
    DefaultMode ->
      runCallbacks annFile "cvc4 --lang=smt2 --incremental" (action cfg)
    RunSolver cmdline ->
      runCallbacks annFile cmdline (action cfg)

standaloneGoalFilename :: String -- ^ Name of function to verify
                       -> String  -- ^ Pretty printed version of block label.
                       -> Integer -- ^ Index of goal to discharge within block
                       -> FilePath
standaloneGoalFilename fn lbl i = fn ++ "_" ++ lbl ++ "_" ++ show i ++ ".smt2"


defineLLVMArgs ::[Typed Ident]
               -> [X86Reg (M.BVType 64)] -- ^ Remaining registers for arguments.
               -> BlockVCG ()
defineLLVMArgs [] _x86Regs = pure ()
defineLLVMArgs (Typed (PrimType (Integer 64)) val : rest) x86Regs =
  case x86Regs of
    [] -> error $ "Ran out of register arguments."
    (reg:restRegs) -> do
      addCommand $ SMT.defineFun (L.identVar val) [] (SMT.bvSort 64)
                                 (varTerm (M.smtRegVar reg))
      defineLLVMArgs rest restRegs
defineLLVMArgs (Typed tp _val : _rest) _x86Regs =
  error $ "Unexpected type " ++ show tp

-- | Verify a block satisfies its specification.
verifyBlock :: CallbackGenerator
            -> Define
            -> Ann.FunctionAnn
            -> L.BasicBlock
            -> ModuleVCG ()
verifyBlock gen lFun funAnn bb = do
  modCtx <- ask
  -- Get block label
  let Just lbl = L.bbLabel bb
  -- Get annotations for this block
  blockAnn <-
    case findBlock funAnn lbl of
      Just b -> pure b
      Nothing -> do
        error $ "Could not find map for block " ++ show lbl
  -- Get LLVM events
  levents <- do
    let ls0 = L.inject lFun
    liftIO $ reverse . L.events <$> execStateT (L.bb2SMT bb) ls0
  -- Lookup memory segment and offset for block.
  segOff <- do
    let mem = moduleMem modCtx
    let absAddr = fromIntegral (Ann.blockAddr blockAnn)
    case resolveAbsoluteAddr mem absAddr of
      Just o -> pure o
      Nothing -> error $ "Could not resolve " ++ show absAddr
  let loc = ExploreLoc { loc_ip = segOff
                       , loc_x87_top = Ann.blockX87Top blockAnn
                       , loc_df_flag = Ann.blockDFFlag blockAnn
                       }
  -- Start running verification condition generator.
  runVCGs gen funAnn loc blockAnn $ do
    -- Add builtin functions
    do addCommand $ M.evenParityDecl
       -- Add read/write operations (independent of registers)
       mapM_ (addCommand . supportedReadDecl)  supportedMemTypes
       mapM_ (addCommand . supportedWriteDecl) supportedMemTypes
    -- Declare registers
    mapM_ addCommand M.declRegs
    -- Declare stack and heap declarations (depends on registers)
    mapM_ addCommand $ mcMemDecls (8+Ann.blockRSPOffset blockAnn)  (Ann.stackSize funAnn)
    -- Declare memory
    addCommand $ SMT.declareConst (M.memVar 0) memSort
    -- Stack stack size is non-negative.
    when (Ann.stackSize funAnn < 0) $ do
      error "Expected non-negative stack size"
    -- Declare constant representing where we return to.
    let returnAddr = addc (varTerm (M.smtRegVar RSP)) (Ann.blockRSPOffset blockAnn)
    supType <- getSupportedType (BVMemRepr (knownNat @8) LittleEndian)
    macawRead "return_addr" returnAddr supType
    -- Declare LLVM arguments in terms of Macaw registers
    defineLLVMArgs (defArgs lFun) x86ArgRegs
    -- Start processing events
    eventsEq levents

$(pure [])

-- | Verify a particular function satisfies its specification.
verifyFunction :: CallbackGenerator
               -> Module
               -- ^ LLVM Module
               -> Ann.FunctionAnn
               -- ^ Annotations to add in mapping LLVM module and
               -- memory layout.
               -> ModuleVCG ()
verifyFunction gen lMod funAnn = do
  modCtx <- ask
  let fnm = Ann.llvmFunName funAnn
  liftIO $ hPutStrLn stderr $ "Analyzing " ++ fnm

  let Just lFun = L.getDefineByName lMod fnm


  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."

  when (defRetType lFun /= L.PrimType (L.Integer 64)) $
    error $ "Return type must be 64-bit integer."

  firstBlock <-
    case defBody lFun of
      [] -> error $ "Expected function to have at least one basic block."
      b:_ -> pure b
  let Just entryLabel = bbLabel firstBlock
  blockAnn <-
    case findBlock funAnn entryLabel of
      Just b -> pure b
      Nothing -> error $ "Could not find map for block " ++ show entryLabel

  let Right addr = getMCAddrOfLLVMFunction (symbolAddrMap modCtx) fnm
  when (toInteger addr /= toInteger (Ann.blockAddr blockAnn)) $ do
    error $ "LLVM function " ++ fnm ++ " does not have expected address: " ++ show addr

  when (Ann.blockRSPOffset blockAnn /= 0) $ do
    liftIO $ warning $ "Function entry offset must be 0."

  forM_ (defBody lFun) $ \bb -> do
    verifyBlock gen lFun funAnn bb

-- | Read an elf from a binary
readElf :: FilePath -> IO (Elf.Elf 64)
readElf path = do
  contents <- BS.readFile path
  case Elf.parseElf contents of
    Elf.ElfHeaderError _ msg ->
      fatalError msg
    Elf.Elf32Res{} -> do
      fatalError "Expected 64-bit elf file."
    Elf.Elf64Res errs e -> do
      mapM_ (warning . show) errs
      unless (Elf.elfMachine e == Elf.EM_X86_64) $ do
        fatalError "Expected a x86-64 binary"
      unless (Elf.elfOSABI e `elem` [Elf.ELFOSABI_LINUX, Elf.ELFOSABI_SYSV]) $ do
        warning "Expected Linux binary"
      pure e

main :: IO ()
main = withVCGArgs $ \metaCfg gen -> do
  e <- readElf $ Ann.binFilePath metaCfg
  let loadOpts = defaultLoadOptions
  case resolveElfContents loadOpts e of
    Left err -> do
      hPutStrLn stderr $
        "Could not interpret Elf file " ++ Ann.binFilePath metaCfg ++ ":\n"
        ++ "  " ++ err
      exitFailure
    Right (warnings, mem, _entry, symbols) -> do
      forM_ warnings $ \w -> do
        hPutStrLn stderr w
      lMod <- L.getLLVMMod (Ann.llvmBCFilePath metaCfg)
      let modCtx = ModuleVCGContext { moduleMem = mem
                                    , symbolAddrMap = Map.fromList
                                                      [ (memSymbolName sym, memSymbolStart sym)
                                                      | sym <- symbols
                                                      ]
                                    }
      runModuleVCG modCtx $ do
        forM_ (Ann.functions metaCfg) $ \funAnn -> do
          verifyFunction gen lMod funAnn
