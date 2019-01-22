{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module VCGLLVM
  ( smtVar
  , getLLVMMod
  , inject
  , bb2SMT
  , getDefineByName
  , events
  , LState
  , locals
  , getFunctionNameFromValSymbol
  , LEvent(..)
  , ppEvent
  ) where

import           Control.Monad.State
import           Data.Bits
import           Data.Int
import           Data.LLVM.BitCode
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Lazy.Builder as Builder
import           GHC.Stack
import           Text.LLVM hiding ((:>))
import qualified What4.Protocol.SMTLib2.Syntax as SMT


import VCGCommon

type Locals = Map.Map Ident SMT.Term

$(pure [])

data LEvent
  = CmdEvent !SMT.Command
  | AllocaEvent !Ident !SMT.Term
  | InvokeEvent !Bool !SMT.Term [SMT.Term] (Maybe (Ident, SMT.Term))
    -- ^ The invoke event takes the address of the function that we are jumping to, the
    -- arguments that are passed in, and the return identifier and value (if any).
  | BranchEvent !SMT.Term !BlockLabel !BlockLabel
    -- ^ Branch event with the predicate being branched on, and the label of the true and false blocks.
  | JumpEvent !BlockLabel
    -- ^ Jump evebnt with the label that we are jumping to.
  | ReturnEvent !(Maybe SMT.Term)
    -- ^ Return with the value being returned.

$(pure [])

ppEvent :: LEvent
        -> String
ppEvent (CmdEvent _) = "cmd"
ppEvent (AllocaEvent _nm _val) = "alloca"
ppEvent (InvokeEvent _ _ _ _) = "invoke"
ppEvent (BranchEvent _ _ _) = "branch"
ppEvent (JumpEvent _) = "jump"
ppEvent (ReturnEvent _) = "return"

$(pure [])

-- TODO: add a predicate to distinguish stack address and heap address
-- TODO: add an array to track bound for each address
-- TODO: arbitray size read/write to memory
data LState = LState
  { locals    :: !Locals
  , memIndex  :: !Integer
    -- ^ Index of memory
  , heap      :: !SMem
  , disjoint  :: ![(SMT.Term, SMT.Term)]
  , events    :: ![LEvent]
  }

$(pure [])

type LStateM a = StateT LState IO a

$(pure [])

addEvent :: LEvent -> LStateM ()
addEvent e = modify $ \s -> s { events = e:events s }

$(pure [])

addCommand :: SMT.Command -> LStateM ()
addCommand cmd = addEvent (CmdEvent cmd)

$(pure [])

readMem :: SMem
        -> SMT.Term -- ^ Address to read
        -> Type
        -> SMT.Term
readMem mem ptr (PrimType (Integer  w))
  | w > 0
  , (w `mod` 8) == 0 = readBVLE mem ptr (toInteger (w `div` 8))
readMem mem ptr (PtrTo _) = readBVLE mem ptr 8
readMem _ _ tp = do
  error $ "readMem: unsupported type " ++ show tp

$(pure [])

smtVar :: Text -> SMT.Term
smtVar = SMT.T . Builder.fromText

$(pure [])

memVar :: Integer -> Text
memVar i = "llvmmem_" <> Text.pack (show i)

memType :: SMT.Sort
memType = SMT.arraySort (SMT.bvSort 64) (SMT.bvSort 8)

-- Inject initial (symbolic) arguments
-- The [String] are arugment name used for this function
inject :: [(Ident,SMT.Term)] -> LState
inject args = do
  let cmd = SMT.declareFun (memVar 0) [] memType
   in LState { locals = Map.fromList args
             , memIndex = 1
             , heap = SMem $ smtVar (memVar 0)
             , disjoint = []
             , events = [CmdEvent cmd]
             }

$(pure [])

localsUpdate :: Ident -> SMT.Term -> LStateM ()
localsUpdate key val = do
  modify $ \s -> s { locals = Map.insert key val (locals s) }

$(pure [])

addDisjointPtr :: SMT.Term -> SMT.Term -> LStateM ()
addDisjointPtr base sz = do
  let end = SMT.bvadd base [sz]
  l <- gets disjoint
  forM_ l $ \(prevBase, prevEnd) -> do
    -- Assert [base,end) is before or after [prevBase, prevEnd)
    addCommand $ SMT.assert $ SMT.or [SMT.bvule prevEnd base, SMT.bvule end prevBase]
  modify $ \s -> s { disjoint = (base,end):disjoint s }

$(pure [])

llvmError :: String -> a
llvmError msg = error ("[LLVM Error] " ++ msg)

$(pure [])

arithOpFunc :: ArithOp
            -> SMT.Term
            -> SMT.Term
            -> SMT.Term
arithOpFunc (Add _uw _sw) x y = SMT.bvadd x [y]
arithOpFunc (Sub _uw _sw) x y = SMT.bvsub x y
arithOpFunc (Mul _uw _sw) x y = SMT.bvmul x [y]
arithOpFunc _ _ _ = llvmError "Not implemented yet"

$(pure [])

asSMTType :: Type -> Maybe SMT.Sort
asSMTType (PtrTo _) = Just (SMT.bvSort 64)
asSMTType (PrimType (Integer i)) | i > 0 = Just $ SMT.bvSort (toInteger i)
asSMTType _ = Nothing

$(pure [])

primEval :: Type
         -> Value
         -> LStateM SMT.Term
primEval _ (ValIdent var@(Ident nm)) = do
  lcls <- gets $ locals
  case Map.lookup var lcls of
    Nothing ->
      llvmError  $ "Not contained in the locals: " ++ nm
    Just v ->
      pure v
primEval (PrimType (Integer w)) (ValInteger i) | w > 0 = do
  pure $ SMT.bvdecimal i (toInteger w)
primEval _ _ = error "TODO: Add more support in primEval"

$(pure [])

bvPrimEval :: Int32
           -> Value
           -> LStateM SMT.Term
bvPrimEval w v = primEval (PrimType (Integer w)) v

$(pure [])

identVar :: Ident -> Text
identVar (Ident nm) = "llvm_" <> Text.pack nm

defineTerm :: Ident -> SMT.Sort -> SMT.Term -> LStateM ()
defineTerm nm tp t = do
  let vnm = identVar nm
  addCommand $ SMT.defineFun vnm [] tp t
  localsUpdate nm (SMT.T (Builder.fromText vnm))

assign2SMT :: Ident -> Instr -> LStateM ()
assign2SMT ident (Arith op (Typed lty lhs) rhs)
  | Just tp <- asSMTType lty = do
      lhsv   <- primEval lty lhs
      rhsv   <- primEval lty rhs
      defineTerm ident tp $ arithOpFunc op lhsv rhsv

assign2SMT ident (ICmp op (Typed lty@(PrimType (Integer w)) lhs) rhs) = do
  lhsv <- primEval lty lhs
  rhsv <- primEval lty rhs
  let r =
        case op of
          Ieq -> SMT.eq [lhsv, rhsv]
          Ine -> SMT.distinct [lhsv, rhsv]
          Iugt -> SMT.bvugt lhsv rhsv
          Iuge -> SMT.bvuge lhsv rhsv
          Iult -> SMT.bvult lhsv rhsv
          Iule -> SMT.bvule lhsv rhsv
          Isgt -> SMT.bvsgt lhsv rhsv
          Isge -> SMT.bvsge lhsv rhsv
          Islt -> SMT.bvslt lhsv rhsv
          Isle -> SMT.bvsle lhsv rhsv
  defineTerm ident (SMT.bvSort (toInteger w)) r
assign2SMT nm (Alloca ty eltCount malign) = do
  let vnm = identVar nm
  addCommand $ SMT.declareFun vnm [] (SMT.bvSort 64)
  let base = smtVar vnm

  let eltSize :: Integer
      eltSize =
        case ty of
          PrimType (Integer i) | i .&. 0x7 == 0 -> toInteger i `shiftR` 3
          PtrTo _ -> 8
          _ -> error $ "Unexpected type " ++ show ty
  -- Total size as a bv64
  totalSize <-
    case eltCount of
      Nothing -> pure $ SMT.bvdecimal eltSize 64
      Just (Typed itp@(PrimType (Integer 64)) i) -> do
        cnt <- primEval itp i
        pure $ SMT.bvmul (SMT.bvdecimal eltSize 64) [cnt]
      Just (Typed itp _) -> do
        error $ "Unexpected count type " ++ show itp

  addDisjointPtr base totalSize
  case malign of
    Nothing -> pure ()
    Just a -> do
      -- Assert base satisfies alignment constraint
      addCommand $ SMT.assert $ SMT.eq [SMT.bvand base [SMT.bvdecimal (toInteger a-1) 64], SMT.bvdecimal 0 64]


  addEvent $ AllocaEvent nm base
  localsUpdate nm base
assign2SMT ident (Load (Typed (PtrTo lty) src) _ord _align) = do
  -- TODO: now assume all ptrs are on stack, maybe add a predicate
  mem <- gets heap
  ptr <- primEval (PtrTo lty) src
  let val = readMem mem ptr lty
  case asSMTType lty of
    Just tp -> defineTerm ident tp val
    Nothing -> error $ "Unexpected type " ++ show lty
assign2SMT ident@(Ident nm) (Call isTailCall retty f args) = do
  -- TODO: Add function called to invoke event.
  fPtrVal <- bvPrimEval 64 f
  let evalArg (Typed lty av) = primEval lty av
  argValues <- mapM evalArg args
  case asSMTType retty of
    Just smtRetType -> do
      let vnm = Text.pack $ "llvm_" ++ nm
      addCommand $ SMT.declareFun vnm [] smtRetType
      let rval = SMT.T (Builder.fromText vnm)
      addEvent $ InvokeEvent isTailCall fPtrVal argValues (Just (ident, rval))
      localsUpdate ident rval
    Nothing -> do
      error $ "assign2SMT given unsupported return type"
assign2SMT _ instr  = do
  error $ "assign2SMT: unsupported instruction: " ++ show instr

$(pure [])

effect2SMT :: HasCallStack => Instr -> LStateM ()
effect2SMT instr =
  case instr of
    Store (Typed llvmTy llvmVal) (Typed llvmPtrTy llvmPtr) _align -> do
      ptr <- primEval llvmPtrTy llvmPtr
      val <- primEval llvmTy    llvmVal
      s <- get
      let SMem newMem =
            case llvmTy of
              PtrTo _ -> do
                writeBVLE (heap s) ptr val 8
              PrimType (Integer w) | (w .&. 0x7) == 0 ->
                writeBVLE (heap s) ptr val (toInteger w `div` 8)
              _ -> error $ "writeMem: unsupported type."
      let cmd = SMT.defineFun (memVar (memIndex s)) [] memType newMem
      put $! s { memIndex = memIndex s + 1
               , heap = SMem (smtVar (memVar (memIndex s)))
               , events = CmdEvent cmd:events s
               }
    Br (Typed _ty cnd) t1 t2 -> do
      cndv <- primEval (PrimType (Integer 1)) cnd
      addEvent $ BranchEvent (SMT.eq [cndv, SMT.bvdecimal 1 1]) t1 t2
    Jump t -> do
      addEvent $ JumpEvent t
    Ret (Typed llvmTy v) -> do
      val <- primEval llvmTy v
      addEvent $ ReturnEvent $ Just val
    RetVoid ->
      addEvent $ ReturnEvent Nothing
    _ -> error "Unsupported instruction."

$(pure [])

stmt2SMT :: Stmt -> LStateM ()
stmt2SMT (Result ident inst _mds) = do
  assign2SMT ident inst
stmt2SMT (Effect instr _mds) = do
  effect2SMT instr

$(pure [])

bb2SMT :: BasicBlock -> LStateM ()
bb2SMT bb = do
  mapM_ stmt2SMT (bbStmts bb)

$(pure [])

getLLVMMod :: FilePath -> IO Module
getLLVMMod path = do
  res <- parseBitCodeFromFile path
  case res of
    Left err -> llvmError $ "Parse LLVM error: " ++ (show err)
    Right llvmMod -> return llvmMod

$(pure [])

getDefineByName :: Module -> String -> Maybe Define
getDefineByName llvmMod name =
  List.find (\d -> defName d == Symbol name) (modDefines llvmMod)

$(pure [])

getFunctionNameFromValSymbol :: Value' lab -> String
getFunctionNameFromValSymbol (ValSymbol (Symbol f)) = f
getFunctionNameFromValSymbol _ = error "Not directly a function"
