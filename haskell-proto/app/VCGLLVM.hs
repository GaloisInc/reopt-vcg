{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
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
  ( getLLVMMod
  , inject
  , bb2SMT
  , getDefineByName
  , events
  , LState
  , disjoint
  , locals
  , getFunctionNameFromValSymbol
  , regNameToSMTSymbol
  , LEvent(..)
  , ppEvent
  ) where

import           Control.Monad.State
import           Data.LLVM.BitCode
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Parameterized.Classes
--import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
--import           Data.Proxy
import           GHC.Stack
--import           System.IO
import           Text.LLVM hiding ((:>))
import           Text.LLVM.PP
import           What4.BaseTypes
import           What4.Interface
--import           What4.Protocol.SMTLib2.Syntax
import           What4.Symbol

import           VCGCommon

type Locals sym = Map.Map Ident (Some (SymExpr sym))

$(pure [])

data LEvent sym
  = AllocaEvent Instr !Ident (SymBV64 sym)
  | InvokeEvent !(SymBV64 sym) [Some (SymExpr sym)] (Maybe (Ident, Some (SymExpr sym)))
    -- ^ The invoke event takes the address of the function that we are jumping to, the
    -- arguments that are passed in, and the return identifier and value (if any).
  | BranchEvent !(SymExpr sym BaseBoolType) !BlockLabel !BlockLabel
  | JumpEvent !BlockLabel
  | ReturnEvent !(Maybe (Some (SymExpr sym)))

$(pure [])

ppEvent :: LEvent sym
        -> String
ppEvent (AllocaEvent _ _nm _val) = "alloca"
ppEvent (InvokeEvent _ _ _) = "invoke"
ppEvent (BranchEvent _ _ _) = "branch"
ppEvent (JumpEvent _) = "jump"
ppEvent (ReturnEvent _) = "return"

$(pure [])

-- TODO: add a predicate to distinguish stack address and heap address
-- TODO: add an array to track bound for each address
-- TODO: arbitray size read/write to memory
data LState sym = LState
  { lsym      :: !sym
  , isBuilder :: !(forall a . (IsSymExprBuilder sym => a) -> a)
  , locals    :: !(Locals sym)
  , heap      :: !(SymMemory sym)
  , disjoint  :: ![Ptr sym]
  , events    :: ![LEvent sym]
  }

$(pure [])

type LStateM sym a = StateT (LState sym) IO a

$(pure [])

io :: (IsSymExprBuilder sym => IO a) -> LStateM sym a
io m = do
  f <- gets isBuilder
  liftIO $ f m

$(pure [])

readMem :: SymMemory sym
        -> Ptr sym
        -> Type
        -> LStateM sym (Some (SymExpr sym))
readMem mem ptr (PrimType (Integer  w))
  | w > 0
  , (w `mod` 8) == 0 = do
      sym <- gets lsym
      Just (Some bw) <- pure $ someNat (toInteger w `div` 3)
      Just LeqProof <- pure $ testLeq (knownNat @1) bw
      io $ Some <$> readMemBVLE sym mem ptr bw
readMem mem ptr (PtrTo _) = do
  sym <- gets lsym
  io $ Some <$> readMemBVLE sym mem ptr (knownNat @8)
readMem _ _ tp = do
  error $ "readMem: unsupported type " ++ show tp

$(pure [])

writeMem :: SymMemory sym
         -> Ptr sym
         -> SymExpr sym tp
         -> BaseTypeRepr tp
         -> LStateM sym (SymMemory sym)
writeMem mem ptr val tp = do
  case tp of
    BaseBVRepr _ -> do
      sym <- gets lsym
      io $ putStrLn "LLVM WriteMem"
      io $ writeMemBVLE sym mem ptr val
    _ -> error $ "writeMem: unsupported type."

$(pure [])

-- Default LLVM register names are consist of digits, which are not valid
-- names in SMTLib. This function tweaks register names by adding a prefix,
-- and then returns a symbol that can be used in SMT.
regNameToSMTSymbol :: String -> SolverSymbol
regNameToSMTSymbol name = newUserSymbol ("r" ++ name)

$(pure [])

-- Inject initial (symbolic) arguments
-- The [String] are arugment name used for this function
inject :: IsSymExprBuilder sym => sym -> [(Ident,Some (SymExpr sym))] -> IO (LState sym)
inject sym args = do
  heap0  <- freshConstant sym (systemSymbol "llvm_mem!") knownRepr
  pure $! LState { lsym = sym
                 , isBuilder = \x -> x
                 , locals = Map.fromList args
                 , heap = heap0
                 , disjoint = []
                 , events = []
                 }

$(pure [])

localsUpdate :: Ident -> SymExpr sym tp -> LStateM sym ()
localsUpdate key val =
  modify $ \s -> s { locals = Map.insert key (Some val) (locals s) }

$(pure [])

addDisjointPtr :: Ptr sym -> LStateM sym ()
addDisjointPtr ptr = modify $ \s -> s { disjoint = ptr:disjoint s }

$(pure [])

addEvent :: LEvent sym -> LStateM sym ()
addEvent e = modify $ \s -> s { events = e:events s }

$(pure [])

llvmError :: String -> a
llvmError msg = error ("[LLVM Error] " ++ msg)

$(pure [])

stackAlloc :: Ident -> Instr -> LStateM sym (SymBV64 sym)
stackAlloc (Ident nm) (Alloca _ty _n _align) = do
  sym <- gets lsym
  freshPtr <- io $ freshConstant sym (regNameToSMTSymbol nm) bv64 --Event
  addDisjointPtr freshPtr
  return freshPtr
stackAlloc _ _ = llvmError "Not a alloca"

$(pure [])

arithOpFunc :: (IsSymExprBuilder sym, 1 <= w)
            => sym
            -> ArithOp
            -> SymExpr sym (BaseBVType w)
            -> SymExpr sym (BaseBVType w)
            -> IO (SymExpr sym (BaseBVType w))
arithOpFunc sym (Add _uw _sw) = bvAdd sym
arithOpFunc sym (Sub _uw _sw) = bvSub sym
arithOpFunc sym (Mul _uw _sw) = bvMul sym
arithOpFunc _ _ = llvmError "Not implemented yet"

$(pure [])

asBaseType :: Type -> Maybe (Some BaseTypeRepr)
asBaseType (PtrTo _) = do
  pure $ Some $ BaseBVRepr (knownNat @64)
asBaseType (PrimType (Integer i)) = do
  Some w <- someNat (toInteger i)
  LeqProof <- testLeq (knownNat :: NatRepr 1) w
  pure $ Some $ BaseBVRepr w
asBaseType _ = Nothing

$(pure [])

primEval :: BaseTypeRepr tp
         -> Value
         -> LStateM sym (SymExpr sym tp)
primEval tpr (ValIdent var@(Ident nm)) = do
  lcls <- gets $ locals
  isb <- gets isBuilder
  case Map.lookup var lcls of
    Nothing ->
      llvmError  $ "Not contained in the locals: " ++ nm
    Just (Some v) -> isb $
      case testEquality tpr (exprType v) of
        Just Refl -> pure v
        Nothing ->
          llvmError
          $  "Bad type assigned to " ++ nm ++ "\n"
          ++ "Assigned type: " ++ show (exprType v) ++ "\n"
          ++ "Declared type: " ++ show tpr
primEval (BaseBVRepr w) (ValInteger i) = do
  sym <- gets lsym
  io $ bvLit sym w i
primEval _ _ = error "TODO: Add more support in primEval"

$(pure [])

bvPrimEval :: 1 <= w
           => NatRepr w
           -> Value
           -> LStateM sym (SymExpr sym (BaseBVType w))
bvPrimEval w v = primEval (BaseBVRepr w) v

$(pure [])

assign2SMT :: Ident -> Instr -> LStateM sym ()
assign2SMT ident (Arith op (Typed lty lhs) rhs) = do
  case asBaseType lty of
    Just (Some (BaseBVRepr w)) -> do
      lhsv   <- bvPrimEval w lhs
      rhsv   <- bvPrimEval w rhs
      sym <- gets lsym
      resv <- io $ arithOpFunc sym op lhsv rhsv
      localsUpdate ident resv
    _ -> error $ "Unsupported type " ++ show lty
assign2SMT ident (ICmp op (Typed lty lhs) rhs) = do
  case asBaseType lty of
    Just (Some (BaseBVRepr w)) -> do
      sym <- gets lsym
      lhsv <- bvPrimEval w lhs
      rhsv <- bvPrimEval w rhs
      r <- io $
        case op of
          Ieq -> bvEq sym lhsv rhsv
          Ine -> bvNe sym lhsv rhsv
          Iugt -> bvUgt sym lhsv rhsv
          Iuge -> bvUge sym lhsv rhsv
          Iult -> bvUlt sym lhsv rhsv
          Iule -> bvUle sym lhsv rhsv
          Isgt -> bvSgt sym lhsv rhsv
          Isge -> bvSge sym lhsv rhsv
          Islt -> bvSlt sym lhsv rhsv
          Isle -> bvSle sym lhsv rhsv
      localsUpdate ident r
    _ -> error $ "Unsupported type " ++ show lty
assign2SMT name allocaVal@(Alloca _ty _n _align) = do
  addr <- stackAlloc name allocaVal
  addEvent $ AllocaEvent allocaVal name addr
  localsUpdate name addr
assign2SMT ident (Load (Typed lty src) _ord _align) = do
  -- TODO: now assume all ptrs are on stack, maybe add a predicate
  mem <- gets heap
  ptr <- primEval bv64 src
  Some val <- readMem mem ptr lty
  localsUpdate ident val
assign2SMT ident@(Ident nm) (Call _tail retty f args) = do
  sym <- gets lsym
  -- TODO: Add function called to invoke event.
  fPtrVal <- primEval bv64 f
  let evalArg (Typed lty av) =
        case asBaseType lty of
          Just (Some tp) ->
            Some <$> primEval tp av
          Nothing ->
            error $ "Could not evaluate type " ++ show lty
  argValues <- mapM evalArg args
  case asBaseType retty of
    Nothing ->
      error $ "Could not evalute type " ++ show retty
    Just (Some tp) -> do
      returnVal <- io $ freshConstant sym (regNameToSMTSymbol nm) tp
      addEvent $ InvokeEvent fPtrVal argValues (Just (ident, Some returnVal))
      localsUpdate ident returnVal
assign2SMT _ instr  = do
  error $ "assign2SMT: unsupported instruction: " ++ show instr

$(pure [])

effect2SMT :: HasCallStack => Instr -> LStateM sym ()
effect2SMT instr =
  case instr of
    Store (Typed _ty1 llvmVal) (Typed llvmTy llvmPtr) _align -> do
      case asBaseType llvmTy of
        Nothing -> do
          error $ "Unsupported type " ++ show llvmTy
        Just (Some tp) -> do
          val <- primEval tp llvmVal
          ptr <- primEval bv64 llvmPtr
          s <- get
          newMem <- writeMem (heap s) ptr val tp
          put $! s { heap = newMem }
    Br (Typed _ty cnd) t1 t2 -> do
      cndv <- primEval BaseBoolRepr cnd
      addEvent $ BranchEvent cndv t1 t2
    Jump t -> do
      addEvent $ JumpEvent t
    Ret (Typed llvmTy v) -> do
      case asBaseType llvmTy of
        Just (Some tp) -> do
          val <- primEval tp v
          addEvent $ ReturnEvent $ Just $ Some val
        Nothing -> do
          error $ "Unsupported type " ++ show llvmTy
    RetVoid ->
      addEvent $ ReturnEvent Nothing
    _ -> error "Unsupported instruction."

$(pure [])

stmt2SMT :: Stmt -> LStateM sym ()
stmt2SMT (Result ident inst _mds) = do
  -- io $ putStrLn $ show inst
  assign2SMT ident inst
stmt2SMT (Effect instr _mds) = do
  -- io $ putStrLn $ show inst
  effect2SMT instr

$(pure [])

bb2SMT :: BasicBlock -> LStateM sym ()
bb2SMT bb = do
  let ?config = Config True True True
  io $ putStrLn $ show $ ppBasicBlock bb
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
