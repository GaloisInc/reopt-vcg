{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module VCGLLVM
  ( getLLVMMod
  , inject
  , bb2SMT
  , getDefineByName
  , events
  , identVar
  , LState
  , getFunctionNameFromValSymbol
  , Event(..)
  , ppEvent
  , AllocaName
  , asSMTType
  ) where

import           Control.Monad.State
import           Data.Bits
import           Data.LLVM.BitCode
import qualified Data.List as List
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.Stack
import           Text.LLVM hiding ((:>))
import qualified Text.LLVM as L
import qualified What4.Protocol.SMTLib2.Syntax as SMT

import           VCGCommon

import           Reopt.VCG.Config (AllocaName(..))

-- | Event from stepping through LLVM block.
data Event
  = CmdEvent !SMT.Command
  | AllocaEvent !Ident !SMT.Term !Integer
    -- ^ `AllocaEvent nm w align` indicates that we should allocate `w` bytes on the stack
    -- and assign the address to @identVar nm@.
    --
    -- The address should be a multiple of `align`.
    --
    -- The identifier is stored so that we can uniquely refer to this identifier.
    --
    -- Users should define @identVar nm@ to a useful value.
  | LoadEvent !SMT.Term !L.Type !Var
    -- ^ `LoadEvent a tp v` indicates that we read `w` bytes fMairom address `a`,
    -- and the value should be assigned to `v` in the SMTLIB.
    --
    -- The variable is a bitvector with width @8*w@.
  | StoreEvent !SMT.Term !L.Type !SMT.Term
    -- ^ `StoreEvent a tp v` indicates that we write the `w` byte value `v` to `a`.
  | InvokeEvent !Bool !L.Symbol [SMT.Term] (Maybe (Ident, Type))
    -- ^ The invoke event takes the address of the function that we
    -- are jumping to, the arguments that are passed in, and the
    -- return identifier and variable to assign the return value to
    -- (if any).
  | BranchEvent !SMT.Term !BlockLabel !BlockLabel
    -- ^ Branch event with the predicate being branched on, and the label of the true and false blocks.
  | JumpEvent !BlockLabel
    -- ^ Jump evebnt with the label that we are jumping to.
  | ReturnEvent !(Maybe SMT.Term)
    -- ^ Return with the value being returned.

ppEvent :: Event
        -> String
ppEvent CmdEvent{} = "cmd"
ppEvent AllocaEvent{} = "alloca"
ppEvent LoadEvent{} = "load"
ppEvent StoreEvent{} = "store"
ppEvent (InvokeEvent _ _ _ _) = "invoke"
ppEvent (BranchEvent _ _ _) = "branch"
ppEvent (JumpEvent _) = "jump"
ppEvent (ReturnEvent _) = "return"

instance Show Event where
  show = ppEvent

-- TODO: add a predicate to distinguish stack address and heap address
-- TODO: arbitray size read/write to memory
data LState = LState
  { disjoint  :: ![(SMT.Term, SMT.Term)]
  , events    :: ![Event]
  }

type LStateM a = StateT LState IO a

addEvent :: Event -> LStateM ()
addEvent e = modify $ \s -> s { events = e:events s }

addCommand :: SMT.Command -> LStateM ()
addCommand cmd = addEvent (CmdEvent cmd)

{-
byteCount :: Type
          -> Integer
byteCount (PrimType (Integer  w))
  | w > 0
  , (w `mod` 8) == 0 =
    toInteger (w `div` 8)
byteCount (PtrTo _) = 8
byteCount tp = do
  error $ "byteCount: unsupported type " ++ show tp
-}

--smtVar :: Text -> SMT.Term
--smtVar = SMT.T . Builder.fromText

--memVar :: Integer -> Text
--memVar i = "llvmmem_" <> Text.pack (show i)

--memType :: SMT.Sort
--memType = SMT.arraySort (SMT.bvSort 64) (SMT.bvSort 8)

-- Inject initial (symbolic) arguments
-- The [String] are arugment name used for this function
inject :: Define -> LState
inject _lFun = do
  LState { disjoint = []
         , events = []
         }

{-
addDisjointPtr :: SMT.Term -> SMT.Term -> LStateM ()
addDisjointPtr base sz = do
  let end = SMT.bvadd base [sz]
  l <- gets disjoint
  forM_ l $ \(prevBase, prevEnd) -> do
    -- Assert [base,end) is before or after [prevBase, prevEnd)
    addCommand $ SMT.assert $ SMT.or [SMT.bvule prevEnd base, SMT.bvule end prevBase]
  modify $ \s -> s { disjoint = (base,end):disjoint s }
-}

llvmError :: String -> a
llvmError msg = error ("[LLVM Error] " ++ msg)

arithOpFunc :: ArithOp
            -> SMT.Term
            -> SMT.Term
            -> SMT.Term
arithOpFunc (Add _uw _sw) x y = SMT.bvadd x [y]
arithOpFunc (Sub _uw _sw) x y = SMT.bvsub x y
arithOpFunc (Mul _uw _sw) x y = SMT.bvmul x [y]
arithOpFunc _ _ _ = llvmError "Not implemented yet"


asSMTType :: Type -> Maybe SMT.Sort
asSMTType (PtrTo _) = Just (SMT.bvSort 64)
asSMTType (PrimType (Integer i)) | i > 0 = Just $ SMT.bvSort (fromIntegral i)
asSMTType _ = Nothing

identVar :: Ident -> Text
identVar (Ident nm) = "llvm_" <> Text.pack nm

-- | Construct an SMT term from a LLVM value
primEval :: HasCallStack
         => Type
         -> Value
         -> LStateM SMT.Term
primEval _ (ValIdent var) = do
  pure $! varTerm (identVar var)
primEval (PrimType (Integer w)) (ValInteger i) = do
  when (w <= 0) $ error "primEval given negative width."
  pure $ SMT.bvdecimal i (fromIntegral w)
primEval tp v  = error $ "TODO: Add more support in primEval:\n"
                    ++ "Type:  " ++ show tp ++ "\n"
                    ++ "Value: " ++ show v


evalTyped :: Typed Value -> LStateM SMT.Term
evalTyped (Typed tp var) = primEval tp var

defineTerm :: Ident -> SMT.Sort -> SMT.Term -> LStateM ()
defineTerm nm tp t = do
  addCommand $ SMT.defineFun (identVar nm) [] tp t

assign2SMT :: Ident -> Instr -> LStateM ()
assign2SMT ident (Arith op (Typed lty lhs) rhs)
  | Just tp <- asSMTType lty = do
      lhsv   <- primEval lty lhs
      rhsv   <- primEval lty rhs
      defineTerm ident tp $ arithOpFunc op lhsv rhsv
assign2SMT ident (ICmp op (Typed lty@(PrimType (Integer w)) lhs) rhs) = do
  when (w <= 0) $ error $ "Unexpected bitwidth " ++ show w
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
  defineTerm ident (SMT.bvSort (fromIntegral w)) r
assign2SMT nm (Alloca ty eltCount malign) = do
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

  let align = case malign of
                Nothing -> 1
                Just a -> toInteger a
  addEvent $ AllocaEvent nm totalSize align
assign2SMT ident (Load (Typed (PtrTo lty) src) _ord _align) = do
  addrTerm <- primEval (PtrTo lty) src
  addEvent $ LoadEvent addrTerm lty (identVar ident)
assign2SMT ident (Call isTailCall retty f args) = do
  -- Evaluate function
  fSym <- case f of
            ValSymbol s -> pure s
            _ -> fail $ "VCG currently only supports directly calls."
  -- Evaluate arguments
  argValues <- traverse evalTyped args
  -- Add invoke event
  addEvent $ InvokeEvent isTailCall fSym argValues (Just (ident, retty))
assign2SMT _ instr  = do
  error $ "assign2SMT: unsupported instruction: " ++ show instr

effect2SMT :: HasCallStack => Instr -> LStateM ()
effect2SMT instr =
  case instr of
    Store llvmVal llvmPtr _ordering _align -> do
      addrTerm <- evalTyped llvmPtr
      valTerm  <- evalTyped llvmVal
      addEvent $ StoreEvent addrTerm (typedType llvmVal) valTerm
    Br (Typed _ty cnd) t1 t2 -> do
      cndTerm <- primEval (PrimType (Integer 1)) cnd
      addEvent $ BranchEvent (SMT.eq [cndTerm, SMT.bvdecimal 1 1]) t1 t2
    Jump t -> do
      addEvent $ JumpEvent t
    Ret (Typed llvmTy v) -> do
      val <- primEval llvmTy v
      addEvent $ ReturnEvent $ Just val
    RetVoid ->
      addEvent $ ReturnEvent Nothing
    _ -> error "Unsupported instruction."

stmt2SMT :: Stmt -> LStateM ()
stmt2SMT (Result ident inst _mds) = do
  assign2SMT ident inst
stmt2SMT (Effect instr _mds) = do
  effect2SMT instr

bb2SMT :: BasicBlock -> LStateM ()
bb2SMT bb = do
  mapM_ stmt2SMT (bbStmts bb)

getLLVMMod :: FilePath -> IO Module
getLLVMMod path = do
  res <- parseBitCodeFromFile path
  case res of
    Left err -> llvmError $ "Parse LLVM error: " ++ (show err)
    Right llvmMod -> return llvmMod

getDefineByName :: Module -> String -> Maybe Define
getDefineByName llvmMod name =
  List.find (\d -> defName d == Symbol name) (modDefines llvmMod)

getFunctionNameFromValSymbol :: Value' lab -> String
getFunctionNameFromValSymbol (ValSymbol (Symbol f)) = f
getFunctionNameFromValSymbol _ = error "Not directly a function"
