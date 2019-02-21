{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder
import qualified Data.Text.Lazy.IO as LText
import qualified Data.Yaml as Yaml
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           Text.LLVM hiding (comment, (:>), Value)
import           Text.LLVM.PP
import           Text.Printf
import qualified What4.Protocol.SMTLib2.Parse as SMTP
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import           Reopt.VCG.Config
import           VCGCommon
import qualified VCGLLVM as L
import qualified VCGMacaw as M


-- Maps LLVM block labels to the information for them.
type BlockMapping = Map String VCGBlockInfo

ppBlock :: BlockLabel -> String
ppBlock (Named (Ident s)) = s
ppBlock (Anon i) = show i

-- | Information about verification of a function.
data VCGConfig = VCGConfig
  { blockMapping :: !BlockMapping
  }

-- | Find a block with the given label in the config.
findBlock :: VCGConfig -> BlockLabel -> Maybe VCGBlockInfo
findBlock cfg lbl = Map.lookup (ppBlock lbl) (blockMapping cfg)

-- | Callback functions for interacting with SMT solver.
data CallbackFns = CallbackFns
  { addCommandCallback :: !(SMT.Command -> IO ())
    -- ^ Invoked to add an SMT command.
    --
    -- These commands must not change the solver out of assert mode.
  , proveFalseCallback :: !(SMT.Term -> String -> IO ())
    -- ^ Invoked when we have a proposition to prove is false for all interprettions.
    --
    -- The message is provide so the user knows the source of the check.
  , proveTrueCallback  :: !(SMT.Term -> String -> IO ())
    -- ^ Invoked when we have a proposition to prove is true for all interprettions.
    --
    -- The message is provide so the user knows the source of the check.
  }

-- | Information that does not change during execution of @VCGMonad@.
data PfConfig = PfConfig
  { cfgConfig :: !VCGConfig
    -- ^ The current configuration for the function.
  , addrEventMap :: !(Map (MemSegmentOff 64) BlockEventInfo)
    -- ^ Set of instruction addresses in this block where reads/writes
    -- should only affect
  , callbackFns :: !CallbackFns
    -- ^ Functions for interacting with SMT solver.
  , allocaOffsetMap :: !(Map AllocaName Integer)
    -- ^ This is a map from allocation names to the offset from the
    -- value in the machine code register `rsp` when the machine code
    -- for the current block starts execution.
  }

-- | State that changes during execution of @VCGMonad@.
data PfState = PfState
  { mcCurAddr :: !(MemSegmentOff 64)
    -- ^ Current instruction address
  , mcMemIndex :: !Integer
    -- ^ Index to give to next memory index
  , mcUsedAllocas :: !(Set AllocaName)
    -- ^ Map names used for allocations to @(b,e)@ where @[b,e)@
    -- represents the hardware range for addresses in the binary.
  , mcOnlyStackFrameIndex :: !Integer
  }

type VCGMonad = ReaderT PfConfig (StateT PfState IO)

addCommand :: SMT.Command -> VCGMonad ()
addCommand cmd = do
  fns <- asks callbackFns
  liftIO $ addCommandCallback fns cmd

-- | @proveFalse p msg@ adds a proof obligation @p@ is false for all interpretations
-- of constants with the message @msg@.
proveFalse :: SMT.Term -> String -> VCGMonad ()
proveFalse p msg = do
  fns <- asks callbackFns
  liftIO $ proveFalseCallback fns p msg

-- | @proveTrue p msg@ adds a proof obligation @p@ is true for all interpretations
-- of constants with the message @msg@.
proveTrue :: SMT.Term -> String -> VCGMonad ()
proveTrue p msg = do
  fns <- asks callbackFns
  liftIO $ proveTrueCallback fns p msg

-- | Assume the propositon is true without requiring it to be proven.
assume :: SMT.Term -> VCGMonad ()
assume p = addCommand $ SMT.assert p

-- | Assert that the functions identified by the LLVM and macaw function pointers
-- are equivalent.
assertFnNameEq :: SMT.Term -> SMT.Term -> VCGMonad ()
assertFnNameEq llvmFun macawIP = undefined llvmFun macawIP

x86ArgRegs :: [X86Reg (M.BVType 64)]
x86ArgRegs = [ RDI, RSI, RDX, RCX, R8, R9 ]

-- | Get SMT term that currently represents memory.
getMCMem :: VCGMonad SMT.Term
getMCMem = do
  idx <- gets mcMemIndex
  pure $! varTerm (M.memVar idx)

-- | @macawWrite addr cnt val@ writes @cnt@ bytes to memory.
--
-- The value written is the @8*cnt@-length bitvector term @val@.
macawWrite :: SMT.Term -> Integer -> SMT.Term -> VCGMonad ()
macawWrite addr byteCount val = do
  idx <- gets mcMemIndex
  modify' $ \s -> s { mcMemIndex = mcMemIndex s + 1 }
  let mem = varTerm (M.memVar idx)
  let newMem | byteCount `elem` [1,2,4,8] =
                 SMT.term_app (memWriteName byteCount) [mem, addr, val]
             | otherwise =
                 writeBVLE (varTerm (M.memVar idx)) addr val byteCount
  addCommand $ SMT.defineFun (M.memVar (idx+1)) [] memSort newMem

-- | Name of function in SMTLIB for writing given number of bytes
memWriteName :: (IsString a, Semigroup a) => Integer -> a
memWriteName byteCount = "mem_write" <> fromString (show (8*byteCount))

-- | Name of function in SMTLIB for reading given number of bytes
memReadName :: (IsString a, Semigroup a) => Integer -> a
memReadName byteCount = "mem_read" <> fromString (show (8*byteCount))

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

-- | Create mem write declaration given number of bytes to write
memReadDecl :: Integer -> SMT.Command
memReadDecl w = do
  SMT.defineFun (memReadName w) [("m", memSort), ("a", ptrSort)] (SMT.bvSort (8*w)) $
    readBVLE (varTerm "m") (varTerm "a") w

-- | Number of bytes in reads that we define via functions.
predefinedMemWidths :: [Integer]
predefinedMemWidths = [1,2,4,8]

-- | @MacawRead addr cnt var@ reads @cnt@ bytes from machine code
-- memory and assigns them to @var@.
macawRead :: SMT.Term -> Integer -> Var -> VCGMonad ()
macawRead addr byteCount valVar = do
  mem <- getMCMem
  let valType = SMT.bvSort (8*byteCount)
  let val | byteCount `elem` predefinedMemWidths  =
              SMT.term_app (memReadName byteCount) [mem, addr]
          | otherwise = readBVLE mem addr byteCount
  addCommand $ SMT.defineFun valVar [] valType val

-- | Create mem write declaration given number of bytes to write
memWriteDecl :: Integer -> SMT.Command
memWriteDecl w = do
  let argTypes = [("m", memSort), ("a", ptrSort), ("v", SMT.bvSort (8*w))]
  SMT.defineFun (memWriteName w) argTypes memSort $
    writeBVLE (varTerm "m") (varTerm "a") (varTerm "v") w

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

-- | @mcMemDecls sz@ adds declarations about the memory.
--
-- It assumes that there is a fresh constant x86reg_RSP declared for the initial RSP, and
-- asserts that @sz < x86reg_RSP < 2^64 - 8@
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
  , SMT.defineFun "stack_high"  [] (SMT.bvSort 64)
      (SMT.bvadd initRSP [SMT.bvdecimal bytesAbove 64])
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
handleEventMatchFailure :: [L.Event] -> [M.Event] -> VCGMonad ()
handleEventMatchFailure [] [] = pure ()
handleEventMatchFailure (lev:_) [] = do
  error $ "LLVM after end of Macaw events:\n"
    ++ L.ppEvent lev
handleEventMatchFailure [] (mev:_) = do
  error $ "Macaw event after end of LLVM events:\n"
    ++ M.ppEvent mev
handleEventMatchFailure (lev:_) (mev:_) = do
  addr <- gets mcCurAddr
  error $ "Incompatible LLVM and Macaw events:\n"
    ++ "LLVM:  " ++ L.ppEvent lev ++ "\n"
    ++ "Macaw " ++ show addr ++ ": " ++ M.ppEvent mev

-- | When that a feature is missing.
missingFeature :: String -> VCGMonad ()
missingFeature msg = liftIO $ hPutStrLn stderr $ "TODO: " ++ msg

-- | @assertEq x y msg@ add a proof obligation named @msg@ asserting that @x@ equals @y@.
assertEq :: SMT.Term -> SMT.Term -> String -> VCGMonad ()
assertEq x y msg = proveFalse (SMT.distinct [x,y]) msg

getCurrentEventInfo :: VCGMonad BlockEventInfo
getCurrentEventInfo = do
  cfg <- ask
  a <- gets mcCurAddr
  case Map.lookup a (addrEventMap cfg) of
    Just info -> pure info
    Nothing -> error $ "Unannotated memory event at " ++ show a

-- | Identifies the LLVM base address of an allocation.
allocaLLVMBaseVar :: AllocaName -> Text
allocaLLVMBaseVar (AllocaName nm) = mconcat ["alloca_", nm, "_llvm_base"]

-- | Identifies the LLVM end address of an allocation.
allocaLLVMEndVar :: AllocaName -> Text
allocaLLVMEndVar (AllocaName nm)  = mconcat ["alloca_", nm, "_llvm_end"]

-- | Identifies the machine code base address of an allocation.
allocaMCBaseVar :: AllocaName -> Text
allocaMCBaseVar (AllocaName nm) = mconcat ["alloca_", nm, "_mc_base"]

-- | Identifies the LLVM end address of an allocation.
allocaMCEndVar :: AllocaName -> Text
allocaMCEndVar (AllocaName nm)  = mconcat ["alloca_", nm, "_mc_end"]

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
assumeLLVMDisjoint :: Range -> AllocaName -> VCGMonad ()
assumeLLVMDisjoint r nm = do
  assume $ isDisjoint r (varTerm (allocaLLVMBaseVar nm), varTerm (allocaLLVMEndVar nm))

-- | This returns an SMT term that denotes the address of an allocation.
getAllocaMCAddr :: AllocaName -> VCGMonad SMT.Term
getAllocaMCAddr nm = do
  allocaMap <- asks $ allocaOffsetMap
  case Map.lookup nm allocaMap of
    Nothing ->
      error $ "Could not find offset of alloca with name: " ++ show nm ++ "\n"
         ++ "Names: " ++ show (Map.keys allocaMap)
    Just o ->
      pure $! if o >= 0 then
                SMT.bvadd initRSP [SMT.bvdecimal o 64]
               else
                SMT.bvsub initRSP (SMT.bvdecimal (negate o) 64)

-- | Process LLVM and macaw events to ensure they are equivalent.
eventsEq :: [L.Event]
         -> [M.Event]
         -> VCGMonad ()
eventsEq levs (M.CmdEvent cmd:mevs) = do
  addCommand cmd
  eventsEq levs mevs
eventsEq levs (M.WarningEvent msg:mevs) = do
  liftIO $ hPutStrLn stderr msg
  eventsEq levs mevs
eventsEq levs (M.InstructionEvent curAddr:mevs) = do
  modify $ \s -> s { mcCurAddr = curAddr }
  eventsEq levs mevs
eventsEq (L.CmdEvent cmd:levs) mevs = do
  addCommand cmd
  eventsEq levs mevs
eventsEq (L.AllocaEvent (Ident nm0) sz _align:levs) mevs = do
  let  nm = AllocaName (Text.pack nm0)
  -- Define base of alloca
  addCommand $ SMT.declareConst (allocaLLVMBaseVar nm) ptrSort
  let llvmBase = varTerm (allocaLLVMBaseVar nm)
  -- Define register alloca is returned to.
  addCommand $ SMT.defineFun ("llvm_" <> allocaNameText nm) [] ptrSort llvmBase
  -- Define end of alloca
  addCommand $ SMT.defineFun (allocaLLVMEndVar nm) [] ptrSort $ SMT.bvadd llvmBase [sz]
  let llvmEnd = varTerm (allocaLLVMEndVar nm)
  -- Assert end calculation did not wrap around.
  assume $ SMT.bvule llvmBase llvmEnd
  -- Get machine code offset.
  mcAddr <- getAllocaMCAddr nm
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
  eventsEq levs mevs
eventsEq levs0 mevs0@(M.ReadEvent mcAddr mcCount macawValVar:mevs) = do
  memEventInfo <- getCurrentEventInfo
  case (memEventInfo, levs0) of
    -- If macaw only access
    (BinaryOnlyAccess, levs) -> do
      -- Assert address is on stack
      do addr <- gets mcCurAddr
         idx <- gets mcOnlyStackFrameIndex
         proveTrue (SMT.term_app (onThisFunStack idx) [mcAddr, SMT.bvdecimal mcCount 64])
           (printf "Machine code read at %s is in unreserved stack space." (show addr))
      -- Define value from reading Macaw heap
      macawRead mcAddr mcCount macawValVar
      -- Process future events.
      eventsEq levs mevs
    (JointStackAccess (aname :: AllocaName), L.LoadEvent llvmLoadAddr llvmCount llvmValVar:levs) -> do
      -- Check alloca is defined
      do used <- gets $ mcUsedAllocas
         when (not (Set.member aname used)) $ error $ "Unknown alloca: " ++ show aname
      -- Assert LLVM address is within @allocaName@
      let llvmAllocBase = varTerm $ allocaLLVMBaseVar aname
      let llvmAllocEnd  = varTerm $ allocaLLVMEndVar  aname
      let mcBase   = varTerm $ allocaMCBaseVar   aname
      let llvmLoadEnd = SMT.bvadd llvmLoadAddr [SMT.bvdecimal llvmCount 64]
      proveTrue (SMT.bvult llvmLoadAddr (SMT.bvhexadecimal (negate llvmCount) 64))
        ("LLVM load address does not overflow")
      proveTrue (SMT.and [ SMT.bvule llvmLoadAddr llvmAllocBase
                         , SMT.bvule llvmLoadEnd  llvmAllocEnd
                         ])
        (printf "LLVM load address is within allocation %s" (show aname))
      -- Assert machine code address is same offset of machine code region as LLVM address.
      assertEq mcAddr (SMT.bvadd mcBase [SMT.bvsub llvmLoadAddr llvmAllocBase])
        ("Machine code stack load address matches expected from LLVM")
      -- Check size of writes are equivalent.
      when (mcCount /= llvmCount) $ do
        error "Bytes read with different number of bytes."
      -- Define value from reading Macaw heap
      macawRead mcAddr mcCount macawValVar
      -- Define LLVM value
      addCommand $ SMT.defineFun llvmValVar [] (SMT.bvSort (8*mcCount)) (varTerm macawValVar)
      -- Process future events.
      eventsEq levs mevs
    (JointStackAccess _,levs) -> do
      handleEventMatchFailure levs mevs0
    (HeapAccess, L.LoadEvent llvmAddr llvmCount llvmValVar:levs) -> do
      -- Assert addresses are the same
      assertEq mcAddr llvmAddr
        ("Machine code heap load address matches expected from LLVM")
      -- Add that macaw points to the heap
      do addr <- gets mcCurAddr
         proveTrue (inHeapSegment mcAddr mcCount)
           (printf "Read from heap at %s is valid." (show addr))

      -- Check size of writes are equivalent.
      when (mcCount /= llvmCount) $ do
        error "Bytes read with different number of bytes."
      -- Define value from reading Macaw heap
      macawRead mcAddr mcCount macawValVar

      -- Define LLVM value returned in terms of macaw value
      addCommand $ SMT.defineFun llvmValVar [] (SMT.bvSort (8*mcCount)) (varTerm macawValVar)
      -- Process future events.
      eventsEq levs mevs
    (HeapAccess,levs) -> do
      handleEventMatchFailure levs mevs0

eventsEq (L.LoadEvent _llvmAddr _llvmCount _llvmValVar:levs)
         (M.CondReadEvent _macawCond _mcAddr _mcCount _macawDef _macawValVar:mevs) = do
  missingFeature "Cond reads are not yet supported."
  -- Process future events.
  eventsEq levs mevs

-- This doesn't match a LLVM read, so we will require it either
-- doesn't occur or is a write to the stack.
eventsEq levs
         (M.CondReadEvent _macawCond _addr _byteCount _defTerm _macawValVar:mevs) = do
  missingFeature "Cond reads are not yet supported."
  eventsEq levs mevs

-- Every LLVM write should have a machine code write (but not
-- necessarily vice versa), we first pattern match on machine code
-- writes.
eventsEq levs0 mevs0@(M.WriteEvent mcAddr mcCount macawVal:mevs) = do
  memEventInfo <- getCurrentEventInfo
  case (memEventInfo, levs0) of
    -- If we are at a stack address, then do following.
    (BinaryOnlyAccess, levs) -> do
      -- Update stack with write.
      macawWrite mcAddr mcCount macawVal
      -- Assert address is on stack
      do addr <- gets mcCurAddr
         idx <- gets mcOnlyStackFrameIndex
         proveTrue (SMT.term_app (onThisFunStack idx) [mcAddr, SMT.bvdecimal mcCount 64])
           (printf "Machine code write at %s is in unreserved stack space." (show addr))
      -- Process next events
      eventsEq levs mevs

    (JointStackAccess allocName, L.StoreEvent llvmAddr llvmCount _llvmVal:levs) -> do
      -- Check the number of bytes written are the same.
      when (llvmCount /= mcCount) $ do
        error "Bytes written have different number of bytes."
      let llvmAllocaBase :: SMT.Term
          llvmAllocaBase = varTerm ("llvm_" <> allocaNameText allocName)
      let mcAllocaBase :: SMT.Term
          mcAllocaBase = varTerm (allocaMCBaseVar allocName)
      let mcAllocaEnd :: SMT.Term
          mcAllocaEnd = varTerm (allocaMCEndVar allocName)
      -- Steps:
      -- Prove: mcAllocaBase + mcCount computation will not overflow.
      proveTrue (SMT.bvult mcAddr (SMT.bvhexadecimal (negate mcCount) 64))
                "Check machine code address does not overflow."
      -- Prove: mcAllocaBase <= mcAddr
      proveTrue (SMT.bvule mcAllocaBase mcAddr)
                "Check address of machine code stack write is at allocation base or higher."
      -- Get address of end of write.
      let mcWriteEnd :: SMT.Term
          mcWriteEnd = SMT.bvadd mcAddr [SMT.bvhexadecimal mcCount 64]
      -- Prove: mcWriteEnd <= allocation end
      proveTrue (SMT.bvule mcWriteEnd mcAllocaEnd)
                "Check machine code write ends before allocation end."
      -- Prove: llvmAddr - llvmAllocaBase = mcAddr - mcAllocaBase
      let llvmOffset = SMT.bvsub llvmAddr llvmAllocaBase
      let mcOffset   = SMT.bvsub   mcAddr   mcAllocaBase
      proveTrue (SMT.eq [llvmOffset, mcOffset])
                "Check we are writing to the same allocation offsets."
      -- Update macaw memory (TODO: See if we really need to do this)
      macawWrite mcAddr mcCount macawVal
      -- Process future events
      eventsEq levs mevs
    (JointStackAccess _, levs) -> do
      handleEventMatchFailure levs mevs0

    (HeapAccess, L.StoreEvent _llvmAddr llvmCount llvmVal:levs) -> do
      when (llvmCount /= mcCount) $ do
        error "Bytes written have different number of bytes."
      missingFeature "Assert machine code and llvm heap write addresses are equal."

      -- Assert values are equal
      assertEq llvmVal macawVal
        ("Machine code heap store matches expected from LLVM")
      -- Update macaw memory
      macawWrite mcAddr mcCount macawVal

      eventsEq levs mevs
    (HeapAccess, levs) ->
      handleEventMatchFailure levs mevs0

eventsEq [L.InvokeEvent _ f lArgs lRet] [M.FetchAndExecuteEvent regs] = do
  let Const mRegIP = regs ^. boundValue X86_IP
  assertFnNameEq f mRegIP
  -- Verify that the arguments should be same.
  -- Note: Here we take the number of arguments from LLVM side,
  -- since the number of arguments in Macaw side seems not explicit.
  -- Also assuming that the # of arguments of LLVM side is less or equal than six.
  when (length lArgs > length x86ArgRegs) $ do
    error $ "Too many arguments."

  let compareArg :: SMT.Term -> X86Reg (M.BVType 64) -> VCGMonad ()
      compareArg la reg = do
        let Const ma = regs^.boundValue reg
        assertEq la ma "Register matches LLVM"
  zipWithM_ compareArg lArgs x86ArgRegs
  -- If LLVM side has a return value, then we assert lRet = mRet as
  -- precondition for the rest program.
  case lRet of
    Just (llvmIdent, PtrTo _) -> do
      -- Returned pointers are assumed to be on heap, so we can assume they are equal.
      let Const mRetVal = regs^.boundValue RAX
      addCommand $ SMT.defineFun (L.identVar llvmIdent) [] (SMT.bvSort 64) mRetVal
    Just (llvmIdent, PrimType (Integer 64)) -> do
      -- Returned pointers are assumed to be on heap, so we can assume they are equal.
      let Const mRetVal = regs^.boundValue RAX
      addCommand $ SMT.defineFun (L.identVar llvmIdent) [] (SMT.bvSort 64) mRetVal
    Just (_llvmIdent, tp) -> do
      error $ "TODO: Add support for return type " ++ show tp
    Nothing -> pure ()
eventsEq [L.JumpEvent lbl] [M.FetchAndExecuteEvent regs] = do
  cfg <- asks $ cfgConfig
  blockInfo <-
    case findBlock cfg lbl of
      Just b -> pure b
      Nothing -> do
        fail $ "Could not find jump target " ++ show lbl
  -- Get term for address associated with this label.
  let llvmMemAddr = SMT.bvhexadecimal (toInteger (blockAddr blockInfo)) 64
  let Const mRegIP = regs ^. boundValue X86_IP
  assertEq llvmMemAddr mRegIP
    ("Jump targets match")
  missingFeature "Assert preconditions for block."
eventsEq [L.ReturnEvent mlret] [M.FetchAndExecuteEvent regs] = do
  -- Assert the IP after the fetch and execute is the return address
  assertEq (getConst (regs^.curIP)) (varTerm "return_addr")
    "Return addresses match"

  -- Assert the stack height at the return is the peak stack height
  assertEq (getConst (regs^.boundValue RSP)) (varTerm "stack_high")
    "Stack height at return matches init"
  --  TODO: Assert callee saved registers have not changed.

  -- Assert the value in RAX is the return value.
  case mlret of
    Nothing -> pure ()
    Just lret -> do
      let Const mret = regs^.boundValue RAX
      assertEq lret mret
       "Return values match"
eventsEq levs mevs = handleEventMatchFailure levs mevs

forceResolveAddr :: Memory w -> MemWord w -> MemSegmentOff w
forceResolveAddr mem a =
  case resolveAbsoluteAddr mem a of
    Just segOff -> segOff
    Nothing -> error $ "Could not resolve " ++ show a

-- | Analyze block events in annotations to associated each address
--with a read with the type of read (mconly stack, translated stack or heap).
extractMemEvents :: Memory 64 -> [BlockEvent] -> Map (MemSegmentOff 64) BlockEventInfo
extractMemEvents mem events = Map.fromList
  [ (forceResolveAddr mem (fromInteger (eventAddr evt)), eventInfo evt)
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

interactiveVerifyGoal :: String -- ^ Name of function to verify
                      -> BlockLabel -- ^ Label of block
                      -> IORef Integer -- ^ Index of goal to discharge within block
                      -> Handle -- ^ Command handle
                      -> Handle -- ^ Response handle
                      -> String
                      -> SMT.Term
                         -- ^ Negation of goal to verify
                      -> IO ()
interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle propName ng =do
  cnt <- readIORef goalCounter
  modifyIORef' goalCounter (+1)
  let fname = standaloneGoalFilename funName lbl cnt
  hPutStrLn stderr $ "Verifying: " ++ propName
  writeCommand cmdHandle $ SMT.checkSatAssuming [ng]
  hFlush cmdHandle
  hPutStrLn stderr $ "  Waiting for response"
  resp <- SMTP.readCheckSatResponse respHandle
  case resp of
    SMTP.SatResponse -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "To see output, run reopt-vcg in standalone mode."
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.UnsatResponse -> do
      hPutStrLn stdout $ "  Verified " ++ fname
    SMTP.UnknownResponse -> do
      hPutStrLn stderr $ "Unknown verification result"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "To see output, run reopt-vcg in standalone mode."
      hPutStrLn stderr $ "The result will be stored in " ++ fname
    SMTP.CheckSatUnsupported -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver does not support check-sat-assuming."
    (SMTP.CheckSatError msg) -> do
      hPutStrLn stderr $ "Verification failed"
      hPutStrLn stderr $ "The SMT solver returned the following message after check-sat-assuming:"
      hPutStrLn stderr ""
      hPutStrLn stderr $ "  " ++ msg

runCallbacks :: String -- ^ Command line
             -> String -- ^ Name of function
             -> BlockLabel
             -> (CallbackFns -> IO a)
             -> IO a
runCallbacks cmdline funName lbl action = do
  goalCounter <- newIORef 0
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
        let fns = CallbackFns
              { addCommandCallback = \cmd -> do
                  writeCommand cmdHandle cmd
              , proveFalseCallback = \p msg -> do
                  interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle msg p
              , proveTrueCallback = \p msg -> do
                  interactiveVerifyGoal funName lbl goalCounter cmdHandle respHandle msg (SMT.not p)
              }
        action fns
    Right _ -> do
      hPutStrLn stderr $ "Unexpected failure running " ++ cmdline
      exitFailure
    Left err -> do
      hPutStrLn stderr $ "Could not execute " ++ cmdline
      hPutStrLn stderr $ "  " ++ show (err :: IOException)
      exitFailure

type FunctionName = String

newtype CallbackGenerator
   = CBG { blockCallbacks :: forall a . FunctionName -> BlockLabel -> (CallbackFns -> IO a) -> IO a }

writeChecksatProblem :: FilePath -- ^ Directory to write file to
                     -> FilePath -- ^ Name of file to export.
                     -> String -- ^ Message to print out with file.
                     -> [SMT.Command] -- ^ Commands
                     -> SMT.Term -- ^ Predicate to assume in final @check-sat-assuming@ call.
                     -> IO ()
writeChecksatProblem outDir fname msg cmds negGoal = do
  hPutStrLn stdout $ fname ++ ": " ++ msg
  bracket (openFile (outDir </> fname) WriteMode) hClose $ \h -> do
    writeCommand h $ comment (fromString msg)
    writeCommand h $ SMT.setLogic SMT.allSupported
    writeCommand h $ SMT.setProduceModels True
    -- Write commands from proof state
    mapM_ (writeCommand h) (reverse cmds)
    writeCommand h $ SMT.checkSatAssuming [negGoal]
    writeCommand h $ SMT.exit

exportCallbacks :: FilePath
                   -- ^ Directory to run file to.
                -> String -- ^ Name of function
                -> BlockLabel
                -> (CallbackFns -> IO a)
                -> IO a
exportCallbacks outDir fn lbl action = do
  goalCounter <- newIORef 0
  cmdRef <- newIORef [] :: IO (IORef [SMT.Command])
  action $! CallbackFns
    { addCommandCallback = \cmd -> do
        modifyIORef' cmdRef $ (cmd:)
    , proveFalseCallback = \p msg -> do
        cnt <- readIORef goalCounter
        modifyIORef' goalCounter (+1)
        cmds <- readIORef cmdRef
        let fname = standaloneGoalFilename fn lbl cnt
        writeChecksatProblem outDir fname msg cmds p
    , proveTrueCallback = \p msg -> do
        cnt <- readIORef goalCounter
        modifyIORef' goalCounter (+1)
        cmds <- readIORef cmdRef
        let fname = standaloneGoalFilename fn lbl cnt
        writeChecksatProblem outDir fname msg cmds (SMT.not p)
    }

runVCGs :: CallbackFns
       -> VCGConfig -- ^ Config for VCG
       -> VCGBlockInfo -- ^ Config for this block
       -> Memory 64
       -> MemSegmentOff 64
          -- ^ Address of first instruction in this block.
       -> VCGMonad ()
       -> IO ()
runVCGs fns cfg thisBlockCfg mem addr action = do
  let allocaMap = Map.fromList
       [ (allocaName a, allocaBinaryOffset a)
       | a <- blockAllocas thisBlockCfg
       ]
  let pfCfg = PfConfig { cfgConfig = cfg
                       , addrEventMap
                         = extractMemEvents mem
                         $ blockEvents thisBlockCfg
                       , callbackFns = fns
                       , allocaOffsetMap = allocaMap
                       }
  let s = PfState { mcCurAddr = addr
                  , mcMemIndex = 0
                  , mcUsedAllocas = Set.empty
                  , mcOnlyStackFrameIndex = 0
                  }
  evalStateT (runReaderT action pfCfg) s

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

parseVCGArgs :: IO (MetaVCGConfig, CallbackGenerator)
parseVCGArgs = do
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

  cfg <- do
    -- Get path to YAML
    vcgPath <-
      case reoptYaml args of
        Nothing -> showError "Missing VCG file to run."
        Just path -> return path
    vcgResult <- Yaml.decodeFileWithWarnings vcgPath
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
  gen <-
    case requestedMode args of
      DefaultMode ->
        pure $ CBG $ runCallbacks "cvc4 --lang=smt2 --incremental"
      ExportMode outdir -> do
        r <- try $ createDirectoryIfMissing True outdir
        case r of
          Right () -> do
            putStrLn $ "Writing output to " ++ outdir
            pure $ CBG $ exportCallbacks outdir
          Left e -> do
            hPutStrLn stderr $ "Error creating output directory: " ++ outdir
            hPutStrLn stderr $ "  " ++ show (e :: IOError)
            exitFailure
      RunSolver cmdline ->
        pure $ CBG $ runCallbacks cmdline

  pure (cfg, gen)

-- | Emit an SMT command to the solver.
writeCommand :: Handle -> SMT.Command -> IO ()
writeCommand h (SMT.Cmd b) =
  LText.hPutStrLn h (Builder.toLazyText b)

standaloneGoalFilename :: String -- ^ Name of function to verify
                       -> BlockLabel -- ^ Label of block
                       -> Integer -- ^ Index of goal to discharge within block
                       -> FilePath
standaloneGoalFilename fn lbl i =
 fn ++ "_" ++ ppBlock lbl ++ "_" ++ show i ++ ".smt2"


defineLLVMArgs ::[Typed Ident]
               -> [X86Reg (M.BVType 64)] -- ^ Remaining registers for arguments.
               -> VCGMonad ()
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
            -> Memory 64
            -> Define
            -> BasicBlock
            -> VCGFunInfo
            -> VCGConfig
            -> IO ()
verifyBlock gen mem lFun bb vfi vcgCfg = do
  let Just lbl = bbLabel bb
  blockCallbacks gen (llvmFunName vfi) lbl $ \fns -> do
    blockHints <-
      case findBlock vcgCfg lbl of
        Just b -> pure b
        Nothing -> do
          error $ "Could not find map for block " ++ show lbl
    let absAddr = fromIntegral (blockAddr blockHints)
    addr <-
      case resolveAbsoluteAddr mem absAddr of
        Just o -> pure o
        Nothing -> fail $ "Could not resolve " ++ show absAddr

    putStrLn "Simulating LLVM blocks ..."
    levents <- do
      do let ?config = Config True True True
         putStrLn $ show $ ppBasicBlock bb
      let ls0 = L.inject lFun
      reverse . L.events <$> execStateT (L.bb2SMT bb) ls0
    -- Assert arguments are equal
    runVCGs fns vcgCfg blockHints mem addr $ do
      -- Add builtin functions
      do addCommand $ M.evenParityDecl
         -- Add read/write operations (independent of registers)
         mapM_ (addCommand . memReadDecl) predefinedMemWidths
         mapM_ (addCommand . memWriteDecl) predefinedMemWidths
      -- Declare registers
      mapM_ addCommand M.declRegs
      -- Declare stack and heap declarations (depends on registers)
      mapM_ addCommand $ mcMemDecls (8+blockHintsRSPOffset blockHints)  (stackSize vfi)
      -- Declare memory
      addCommand $ SMT.declareConst (M.memVar 0) memSort
      -- Stack stack size is non-negative.
      when (stackSize vfi < 0) $ do
        error "Expected non-negative stack size"
      -- Declare constant representing where we return to.
      macawRead (varTerm (M.smtRegVar RSP)) 8 "return_addr"
      -- Declare LLVM arguments in terms of Macaw registers
      defineLLVMArgs (defArgs lFun) x86ArgRegs
      -- Start processing events
      eventsEq levents (M.blockEvents addr (blockCodeSize blockHints))

-- | Verify a particular function satisfies its specification.
verifyFunction :: Module
               -- ^ LLVM Module
               -> Memory 64
               -> CallbackGenerator
               -> VCGFunInfo
                  -- ^ Specification of function.
               -> IO ()
verifyFunction lMod mem gen vfi = do

  let llvmBlockMap :: Map String VCGBlockInfo
      llvmBlockMap = Map.fromList
        [ (blockLabel b, b) | b <- blocks vfi ]
{-
  addr <-
    case Map.lookup (BSC.pack (macawFunName vfi)) funMap of
      Just addr ->
        pure addr
      Nothing ->
        fatalError
            $  "Unknown Macaw function: " ++ macawFunName vfi ++ "\n"
            ++ "Available functions:\n"
            ++ unlines ((\x -> "  " ++ BSC.unpack x) <$> Map.keys funMap)
-}

  hPutStrLn stderr $ "Analyzing " ++ llvmFunName vfi

  let Just lFun = L.getDefineByName lMod (llvmFunName vfi)


  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."
  let vcgCfg =  VCGConfig { blockMapping = llvmBlockMap
                          }
  -- Check annotations of first block to ensure
  firstBlock <-
    case defBody lFun of
      [] -> error $ "Expected function to have at least one basic block."
      b:_ -> pure b
  let Just lbl = bbLabel firstBlock
  blockHints <-
    case findBlock vcgCfg lbl of
      Just b -> pure b
      Nothing -> error $ "Could not find map for block " ++ show lbl
  when (blockHintsRSPOffset blockHints /= 0) $ do
    warning $ "Function entry offset must be 0."
  forM_ (defBody lFun) $ \bb -> do
    verifyBlock gen mem lFun bb vfi vcgCfg

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
main = do
  (metaCfg, gen) <- parseVCGArgs
  putStrLn $ show metaCfg
  e <- readElf $ binFilePath metaCfg
  let loadOpts = defaultLoadOptions
  case resolveElfContents loadOpts e of
    Left err -> do
      hPutStrLn stderr $
        "Could not interpret Elf file " ++ binFilePath metaCfg ++ ":\n"
        ++ "  " ++ err
      exitFailure
    Right (warnings, mem, _entry, _symbols) -> do
      forM_ warnings $ \w -> do
        hPutStrLn stderr w
      lMod <- L.getLLVMMod (llvmBCFilePath metaCfg)
      forM_ (functions metaCfg) $ \vfi -> do
        verifyFunction lMod mem gen vfi
