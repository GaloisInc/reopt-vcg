{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

ppBlock :: BlockLabel -> String
ppBlock (Named (Ident s)) = s
ppBlock (Anon i) = show i

-- | Find a block with the given label in the config.
findBlock :: Ann.VCGFunInfo -> BlockLabel -> Maybe Ann.VCGBlockInfo
findBlock cfg lbl = Map.lookup (ppBlock lbl) (Ann.blocks cfg)

-- | Callback functions for interacting with SMT solver.
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

-- | Information that does not change during execution of @BlockVCG@.
data BlockVCGContext = BlockVCGContext
  { curFunAnnotations :: !Ann.VCGFunInfo
    -- ^ Annotations for the current function we are verifying.
  , addrEventMap :: !(Map (MemSegmentOff 64) Ann.BlockEventInfo)
    -- ^ Maps address of instruction to information about memory
    -- reads/writes at that address.
  , callbackFns :: !CallbackFns
    -- ^ Functions for interacting with SMT solver.
  , allocaOffsetMap :: !(Map Ann.AllocaName Integer)
    -- ^ This is a map from allocation names to the offset from the
    -- value in the machine code register `rsp` when the machine code
    -- for the current block starts execution.
  , llvmSymbolToMCAddrMap :: !(Map BS.ByteString (MemSegmentOff 64))
    -- ^ Maps LLVM symbol names to the address that we expect the
    -- function to be at.
  }

-- | State that changes during execution of @BlockVCG@.
data BlockVCGState = BlockVCGState
  { mcCurAddr :: !(MemSegmentOff 64)
    -- ^ Current instruction address
  , mcCurSize :: !(MemWord 64)
    -- ^ Size of current instruction
  , mcMemIndex :: !Integer
    -- ^ Index to give to next memory index
  , mcUsedAllocas :: !(Set Ann.AllocaName)
    -- ^ Map names used for allocations to @(b,e)@ where @[b,e)@
    -- represents the hardware range for addresses in the binary.
  , mcOnlyStackFrameIndex :: !Integer
  , mcEvents :: ![M.Event]
  }

type BlockVCG = ReaderT BlockVCGContext (StateT BlockVCGState IO)

addCommand :: SMT.Command -> BlockVCG ()
addCommand cmd = do
  fns <- asks callbackFns
  liftIO $ addCommandCallback fns cmd

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
  addrMap <- asks $ llvmSymbolToMCAddrMap
  let Right addr = getMCAddrOfLLVMFunction addrMap nm
  let expectedAddrTerm = SMT.bvhexadecimal (toInteger addr) 64
  assertEq expectedAddrTerm macawIP ("Equivalence of function: " ++ nm)

x86ArgRegs :: [X86Reg (M.BVType 64)]
x86ArgRegs = [ RDI, RSI, RDX, RCX, R8, R9 ]

-- | Get SMT term that currently represents memory.
getMCMem :: BlockVCG SMT.Term
getMCMem = do
  idx <- gets mcMemIndex
  pure $! varTerm (M.memVar idx)

type KnownMemInfo = (Some MemRepr, (String, SMT.Sort, SMT.Term, SMT.Term))

supportedBV :: (1 <= w) => NatRepr w -> KnownMemInfo
supportedBV w =
  ( Some (BVMemRepr w LittleEndian)
  , ( "bv" <> show (8*natValue w)
    , SMT.bvSort (8*natValue w)
    , readBVLE (varTerm "m") (varTerm "a") (natValue w)
    , writeBVLE (varTerm "m") (varTerm "a") (varTerm "v") (natValue w)
    )
  )

-- | Types that may appear in reads/writes.
supportedMemTypes :: Map (Some MemRepr) (String, SMT.Sort, SMT.Term, SMT.Term)
supportedMemTypes = Map.fromList $
  [ supportedBV (knownNat @1)
  , supportedBV (knownNat @2)
  , supportedBV (knownNat @4)
  , supportedBV (knownNat @8)
  ]

-- | Create mem write declaration given number of bytes to write
memWriteDecl :: KnownMemInfo -> SMT.Command
memWriteDecl (Some _, (suf, typeSort, _readDef, writeDef)) = do
  let argTypes = [("m", memSort), ("a", ptrSort), ("v", typeSort)]
  SMT.defineFun ("mem_write" <> fromString suf) argTypes memSort writeDef

-- | @macawWrite addr cnt val@ writes @cnt@ bytes to memory.
--
-- The value written is the @8*cnt@-length bitvector term @val@.
macawWrite :: SMT.Term -> MemRepr tp -> SMT.Term -> BlockVCG ()
macawWrite addr memType val = do
  idx <- gets mcMemIndex
  modify' $ \s -> s { mcMemIndex = mcMemIndex s + 1 }
  let mem = varTerm (M.memVar idx)
  case Map.lookup (Some memType) supportedMemTypes of
    Nothing -> error $ "Unexpected type " ++ show memType
    Just (suf, _, _, _) -> do
      let newMem = SMT.term_app ("mem_write" <> fromString suf) [mem, addr, val]
      addCommand $ SMT.defineFun (M.memVar (idx+1)) [] memSort newMem

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
memReadDecl :: KnownMemInfo  -> SMT.Command
memReadDecl (Some _, (suf, resSort, readDef, _writeDef)) = do
  let nm = "mem_read" <> fromString suf
  let args = [("m", memSort), ("a", ptrSort)]
  SMT.defineFun nm args resSort readDef

-- | @MacawRead addr cnt var@ reads @cnt@ bytes from machine code
-- memory and assigns them to @var@.
macawRead :: SMT.Term -> MemRepr tp -> Var -> BlockVCG SMT.Sort
macawRead addr memType valVar = do
  mem <- getMCMem
  case Map.lookup (Some memType) supportedMemTypes of
    Nothing -> error $ "Unexpected type " ++ show memType
    Just (suf, valSort, _, _) -> do
      let val = SMT.term_app ("mem_read" <> fromString suf) [mem, addr]
      addCommand $ SMT.defineFun valVar [] valSort val
      pure valSort

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

-- | This returns an SMT term that denotes the address of an allocation.
getAllocaMCAddr :: Ann.AllocaName -> BlockVCG SMT.Term
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

-- | Check if LLVM type and Macaw types are compatible.
typeCompat :: L.Type -> MemRepr tp -> Bool
typeCompat (L.PrimType (L.Integer lw)) (BVMemRepr mw _) =
  toInteger lw == intValue mw
typeCompat (L.PtrTo tp) (BVMemRepr mw _) =
  intValue mw == 64
typeCompat (L.PrimType (L.FloatType L.Float)) (FloatMemRepr SingleFloatRepr _) =
  True
typeCompat (L.PrimType (L.FloatType L.Double)) (FloatMemRepr DoubleFloatRepr _) =
  True
typeCompat (L.PrimType (L.FloatType L.X86_fp80)) (FloatMemRepr X86_80FloatRepr _) =
  True
typeCompat (L.Vector ln ltp) (PackedVecMemRepr mn mtp) =
  toInteger ln == intValue mn && typeCompat ltp mtp

processMCEvents :: [M.Event] -> BlockVCG [M.Event]
processMCEvents (M.CmdEvent cmd:mevs) = do
  addCommand cmd
  processMCEvents mevs
processMCEvents (M.WarningEvent msg:mevs) = do
  liftIO $ hPutStrLn stderr msg
  processMCEvents mevs
processMCEvents (M.InstructionEvent curAddr:mevs) = do
  modify $ \s -> s { mcCurAddr = curAddr }
  processMCEvents mevs
processMCEvents (M.MCOnlyStackReadEvent mcAddr tp macawValVar:mevs) = do
  -- Assert address is on stack
  do addr <- gets mcCurAddr
     idx <- gets mcOnlyStackFrameIndex
     let sz = memReprBytes tp
     proveTrue (SMT.term_app (onThisFunStack idx) [mcAddr, SMT.bvdecimal sz 64])
               (printf "Machine code read at %s is in unreserved stack space." (show addr))
  -- Define value from reading Macaw heap
  _ <- macawRead mcAddr tp macawValVar
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

setMCEvents :: [M.Event] -> BlockVCG ()
setMCEvents evts = do
  modify $ \s -> s { mcEvents = evts }

getMCEvents :: BlockVCG [M.Event]
getMCEvents = do
  mevents <- gets mcEvents
  mevents' <- processMCEvents mevents
  setMCEvents mevents'
  pure mevents'

popMCEvent :: BlockVCG M.Event
popMCEvent = do
  evts <- getMCEvents
  case evts of
    [] -> error $ "Unexpected end of machine code events."
    (h:r) -> do
      setMCEvents r
      pure h

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
      smtType <- macawRead mcAddr mcType macawValVar
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
      smtType <- macawRead mcAddr mcType macawValVar
      -- Define LLVM value returned in terms of macaw value
      addCommand $ SMT.defineFun llvmValVar [] smtType (varTerm macawValVar)
      -- Process future events.
      eventsEq levs
    _ -> do
      handleEventMatchFailure levs0 mevt

{-
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
-}

eventsEq levs0@(L.StoreEvent llvmAddr llvmType llvmVal:levs) = do
  mevt <- popMCEvent
  case mevt of
    M.JointStackWriteEvent mcAddr mcType mcVal allocName -> do
      -- Check the number of bytes written are the same.
      unless (typeCompat llvmType mcType) $ do
        error "Machine code and LLVM writes have different types."
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
      -- TODO: Check types agree.
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

eventsEq levs0@[L.InvokeEvent _ f lArgs lRet]  = do
  mevts <- getMCEvents
  case mevts of
    [M.FetchAndExecuteEvent regs] -> do
      let Const mRegIP = regs ^. boundValue X86_IP
      assertFnNameEq f mRegIP
      -- Verify that the arguments should be same.
      -- Note: Here we take the number of arguments from LLVM side,
      -- since the number of arguments in Macaw side seems not explicit.
      -- Also assuming that the # of arguments of LLVM side is less or equal than six.
      when (length lArgs > length x86ArgRegs) $ do
        error $ "Too many arguments."

      let compareArg :: SMT.Term -> X86Reg (M.BVType 64) -> BlockVCG ()
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
    [] -> error $ "Unexpected end of events."
    mevt:_ -> handleEventMatchFailure levs0 mevt
eventsEq levs0@[L.JumpEvent lbl]  = do
  mevts <- getMCEvents
  case mevts of
    [M.FetchAndExecuteEvent regs] -> do

      fnAnn <- asks $ curFunAnnotations
      blockInfo <-
        case findBlock fnAnn lbl of
          Just b -> pure b
          Nothing -> do
            fail $ "Could not find jump target " ++ show lbl
      -- Get term for address associated with this label.
      let llvmMemAddr = SMT.bvhexadecimal (toInteger (Ann.blockAddr blockInfo)) 64
      let Const mRegIP = regs ^. boundValue X86_IP
      assertEq llvmMemAddr mRegIP "Jump targets match"
      missingFeature "Assert preconditions for block."
    [] -> error $ "Unexpected end of events."
    mevt:_ -> handleEventMatchFailure levs0 mevt
eventsEq levs0@[L.ReturnEvent mlret] = do
  mevts <- getMCEvents
  case mevts of
    [M.FetchAndExecuteEvent regs] -> do
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
          assertEq lret mret "Return values match"
    [] -> error $ "Unexpected end of events."
    mevt:_ -> handleEventMatchFailure levs0 mevt
eventsEq (lev:_) = do
  error $ "Unexpected LLVM event:\n" ++ L.ppEvent lev
eventsEq [] = do
  mevts <- getMCEvents
  case mevts of
    [] -> pure ()
    mev:_ -> do
      error $ "Macaw event after end of LLVM events:\n" ++ M.ppEvent mev

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

interactiveVerifyGoal :: String -- ^ Name of function to verify
                      -> String -- ^ Label of block
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

runCallbacks :: String -- ^ Command line for running SMT solver
             -> String -- ^ Name of function
             -> String -- ^ Name of block
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

-- | Tool for running verification conditions.
-- This has a
newtype CallbackGenerator
   = CBG { blockCallbacks :: forall a . FunctionName -> String-> (CallbackFns -> IO a) -> IO a }

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
                -> String
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

-- | Information needed for checking equivalence of entire module
data ModuleInfo = ModuleInfo { moduleMem :: !(Memory 64)
                               -- ^ Machine code memory
                             , symbolAddrMap :: !(Map BS.ByteString (MemSegmentOff 64))
                               -- ^ Maps bytes to the symbol name
                             }

{-
-- | Information about a resolved blokck includes the LLVM basic block, the machine code
-- segment offset and annotations.
data ResolvedBasicBlock = RBB { rbbLLVM :: !L.BasicBlock
                              , rbbMCSegOff :: !(MemSegmentOff 64)
                              , rbbAnnotations :: !Ann.VCGBlockInfo
                              }

--  Resolve information about an LLVM basic block
resolveLLVMBasicBlock
  :: Memory 64
  -> Ann.VCGFunInfo
  -> L.BasicBlock
  -> Either String ResolvedBasicBlock
resolveLLVMBasicBlock mem funAnn bb = do
  lbl <- case L.bbLabel bb of
           Just lbl -> Right lbl
           Nothing -> Left $ "Could not parse LLVM label within " ++ Ann.llvmFunName funAnn
  blockAnn <-
    case findBlock funAnn lbl of
      Just b -> Right b
      Nothing -> Left $ "Could not find annotations for block " ++ show lbl
  segOff <- do
    let absAddr = fromIntegral (Ann.blockAddr blockAnn)
    case resolveAbsoluteAddr mem absAddr of
      Just o -> Right o
      Nothing -> Left $ "Could not resolve " ++ show absAddr
  Right $! RBB { rbbLLVM = bb
               , rbbMCSegOff = segOff
               , rbbAnnotations = blockAnn
               }
-}

runVCGs :: CallbackGenerator
        -> ModuleInfo -- ^ Information needed to verify module.
        -> Ann.VCGFunInfo -- ^ Annotations for the function we are verifying.
        -> MemSegmentOff 64 -- ^ Segment offset of this block.
        -> Ann.VCGBlockInfo -- ^ Annotations for the block we are verifying.
        -> BlockVCG ()
        -> IO ()
runVCGs gen modInfo funAnn thisSegOff blockAnn action = do
  let mem = moduleMem modInfo
  blockCallbacks gen (Ann.llvmFunName funAnn) (Ann.blockLabel blockAnn) $ \fns -> do
    let allocaMap = Map.fromList
          [ (Ann.allocaName a, Ann.allocaBinaryOffset a)
          | a <- Ann.blockAllocas blockAnn
          ]
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
                              , allocaOffsetMap = allocaMap
                              , llvmSymbolToMCAddrMap = symbolAddrMap modInfo
                              }
    let s = BlockVCGState { mcCurAddr = thisSegOff
                          , mcCurSize = 0
                          , mcMemIndex = 0
                          , mcUsedAllocas = Set.empty
                          , mcOnlyStackFrameIndex = 0
                          , mcEvents = M.blockEvents blockMap thisSegOff (Ann.blockCodeSize blockAnn)
                          }
    evalStateT (runReaderT action ctx) s

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

parseVCGArgs :: IO (Ann.MetaVCGConfig, CallbackGenerator)
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
            -> ModuleInfo
               -- ^ Information needed to verify module
            -> Define
            -> Ann.VCGFunInfo
            -> L.BasicBlock
            -> IO ()
verifyBlock gen modInfo lFun funAnn bb = do
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
    reverse . L.events <$> execStateT (L.bb2SMT bb) ls0
  -- Lookup memory segment and offset for block.
  segOff <- do
    let mem = moduleMem modInfo
    let absAddr = fromIntegral (Ann.blockAddr blockAnn)
    case resolveAbsoluteAddr mem absAddr of
      Just o -> pure o
      Nothing -> error $ "Could not resolve " ++ show absAddr
  -- Start running verification condition generator.
  runVCGs gen modInfo funAnn segOff blockAnn $ do
    -- Add builtin functions
    do addCommand $ M.evenParityDecl
       -- Add read/write operations (independent of registers)
       mapM_ (addCommand . memReadDecl)  (Map.toList supportedMemTypes)
       mapM_ (addCommand . memWriteDecl) (Map.toList supportedMemTypes)
    -- Declare registers
    mapM_ addCommand M.declRegs
    -- Declare stack and heap declarations (depends on registers)
    mapM_ addCommand $ mcMemDecls (8+Ann.blockHintsRSPOffset blockAnn)  (Ann.stackSize funAnn)
    -- Declare memory
    addCommand $ SMT.declareConst (M.memVar 0) memSort
    -- Stack stack size is non-negative.
    when (Ann.stackSize funAnn < 0) $ do
      error "Expected non-negative stack size"
    -- Declare constant representing where we return to.
    _ <- macawRead (varTerm (M.smtRegVar RSP)) (BVMemRepr (knownNat @8) LittleEndian) "return_addr"
    -- Declare LLVM arguments in terms of Macaw registers
    defineLLVMArgs (defArgs lFun) x86ArgRegs
    -- Start processing events
    eventsEq levents

-- | Verify a particular function satisfies its specification.
verifyFunction :: CallbackGenerator
               -> Module
               -- ^ LLVM Module
               -> ModuleInfo
                  -- ^ Information needed to verify module.
               -> Ann.VCGFunInfo
                  -- ^ Hints to add in mapping LLVM module and memory layout.
               -> IO ()
verifyFunction gen lMod modInfo funAnn = do
  let fnm = Ann.llvmFunName funAnn
  hPutStrLn stderr $ "Analyzing " ++ fnm

  let Just lFun = L.getDefineByName lMod fnm


  when (length (defArgs lFun) > length x86ArgRegs) $ do
    error $ "Too many arguments."
  firstBlock <-
    case defBody lFun of
      [] -> error $ "Expected function to have at least one basic block."
      b:_ -> pure b
  let Just entryLabel = bbLabel firstBlock
  blockAnn <-
    case findBlock funAnn entryLabel of
      Just b -> pure b
      Nothing -> error $ "Could not find map for block " ++ show entryLabel

  let Right addr = getMCAddrOfLLVMFunction (symbolAddrMap modInfo) fnm
  when (toInteger addr /= toInteger (Ann.blockAddr blockAnn)) $ do
    error $ "LLVM function " ++ fnm ++ " does not have expected address: " ++ show addr

  when (Ann.blockHintsRSPOffset blockAnn /= 0) $ do
    warning $ "Function entry offset must be 0."

  forM_ (defBody lFun) $ \bb -> do
    verifyBlock gen modInfo lFun funAnn bb

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
      let modInfo = ModuleInfo { moduleMem = mem
                               , symbolAddrMap = Map.fromList
                                 [ (memSymbolName sym, memSymbolStart sym)
                                 | sym <- symbols
                                 ]
                               }
      forM_ (Ann.functions metaCfg) $ \funAnn -> do
        verifyFunction gen lMod modInfo funAnn
