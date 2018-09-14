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
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module VCGLLVM
  ( getLLVMMod
  , inject
  , blocks2SMT
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

import           Control.Monad (forM_)
import           Control.Monad.State
import           Data.LLVM.BitCode
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Some
import           Data.Proxy
import           GHC.Stack
import           System.IO
import           Text.LLVM hiding ((:>))
import           Text.LLVM.PP
import qualified Text.Read as Read
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import           What4.BaseTypes
import           What4.Interface
import           What4.Symbol

import           VCGCommon


type Locals sym = Map.Map Ident (Some (SymExpr sym))

data LEvent sym
  = AllocaEvent Instr !Ident (SymBV64 sym)
  | InvokeEvent !(SymBV64 sym) [Some (SymExpr sym)] (Maybe (Ident, Some (SymExpr sym)))
    -- ^ The invoke event takes the address of the function that we are jumping to, the
    -- arguments that are passed in, and the return identifier and value (if any).
  | BranchEvent !(SymExpr sym BaseBoolType) !BlockLabel !BlockLabel
  | JumpEvent !BlockLabel
  | ReturnEvent !(Maybe (Some (SymExpr sym)))

ppEvent :: LEvent sym
        -> String
ppEvent (AllocaEvent _ nm val) = "alloca"
ppEvent (InvokeEvent _ _ _) = "invoke"
ppEvent (BranchEvent _ _ _) = "branch"
ppEvent (JumpEvent _) = "jump"
ppEvent (ReturnEvent _) = "return"

readMem :: IsSymExprBuilder sym
        => sym
        -> SymMemory sym
        -> Ptr sym
        -> Type
        -> LStateM sym (Some (SymExpr sym))
readMem sym mem ptr (PrimType (Integer  w))
  | w > 0
  , (w `mod` 8) == 0 = do
      Just (Some w) <- pure $ someNat (toInteger w `div` 3)
      Just LeqProof <- pure $ testLeq (knownNat @1) w
      io $ Some <$> readMemBVLE sym mem ptr w
readMem sym mem ptr (PtrTo _) = do
  io $ Some <$> readMemBVLE sym mem ptr (knownNat @8)

readMem _ _ _ tp = do
  error $ "readMem: unsupported type " ++ show tp

writeMem :: IsSymExprBuilder sym
         => sym
         -> SymMemory sym
         -> Ptr sym
         -> SymExpr sym tp
         -> LStateM sym (SymMemory sym)
writeMem sym mem ptr val =
  case exprType val of
    BaseBVRepr _ -> do
      io $ putStrLn "LLVM WriteMem"
      io $ writeMemBVLE sym mem ptr val
    _ -> error $ "writeMem: unsupported type."

-- TODO: add a predicate to distinguish stack address and heap address
-- TODO: add an array to track bound for each address
-- TODO: arbitray size read/write to memory
data LState sym = LState
  { locals   :: Locals sym
  , heap     :: SymMemory sym
  , disjoint :: [Ptr sym]
  , events   :: [LEvent sym]
  }

type LStateM sym a = StateT (LState sym) IO a

type LStateBV64M sym = LStateM sym (SymBV64 sym)

io :: IO a -> LStateM sym a
io = liftIO

  -- Default LLVM register names are consist of digits, which are not valid
-- names in SMTLib. This function tweaks register names by adding a prefix,
-- and then returns a symbol that can be used in SMT.
regNameToSMTSymbol :: String -> SolverSymbol
regNameToSMTSymbol name = newUserSymbol ("r" ++ name)

-- Inject initial (symbolic) arguments
-- The [String] are arugment name used for this function
inject :: IsSymExprBuilder sym => sym -> [(Ident,Some (SymExpr sym))] -> IO (LState sym)
inject sym args = do
  heap0  <- freshConstant sym (systemSymbol "llvm_mem!") knownRepr
  pure $! LState { locals = Map.fromList args
                 , heap = heap0
                 , disjoint = []
                 , events = []
                 }


localsUpdate :: IsSymExprBuilder sym => Ident -> SymExpr sym tp -> LStateM sym ()
localsUpdate key val =
  modify $ \s -> s { locals = Map.insert key (Some val) (locals s) }

addDisjointPtr :: IsSymExprBuilder sym => (Ptr sym) -> LStateM sym ()
addDisjointPtr ptr = modify $ \s -> s { disjoint = ptr:disjoint s }

addEvent :: IsSymExprBuilder sym => LEvent sym -> LStateM sym ()
addEvent e = modify $ \s -> s { events = e:events s }

stackAlloc :: IsSymExprBuilder sym => sym -> Ident -> Instr -> LStateBV64M sym
stackAlloc sym (Ident nm) (Alloca _ty _n _align) = do
  freshPtr <- io $ freshConstant sym (regNameToSMTSymbol nm) bv64 --Event
  addDisjointPtr freshPtr
  return freshPtr
stackAlloc _ _ _ = llvmError "Not a alloca"

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

asBaseType :: Type -> Maybe (Some BaseTypeRepr)
asBaseType (PtrTo _) = do
  pure $ Some $ BaseBVRepr (knownNat @64)
asBaseType (PrimType (Integer i)) = do
  Some w <- someNat (toInteger i)
  LeqProof <- testLeq (knownNat :: NatRepr 1) w
  pure $ Some $ BaseBVRepr w
asBaseType _ = Nothing


primEval :: IsSymExprBuilder sym
         => sym
         -> BaseTypeRepr tp
         -> Value
         -> LStateM sym (SymExpr sym tp)
primEval _sym tpr (ValIdent var@(Ident nm)) = do
  lcls <- gets $ locals
  case Map.lookup var lcls of
    Nothing ->
      llvmError  $ "Not contained in the locals: " ++ nm
    Just (Some v) ->
      case testEquality tpr (exprType v) of
        Just Refl -> pure v
        Nothing ->
          llvmError
          $  "Bad type assigned to " ++ nm ++ "\n"
          ++ "Assigned type: " ++ show (exprType v) ++ "\n"
          ++ "Declared type: " ++ show tpr
primEval sym (BaseBVRepr w) (ValInteger i) = do
  io $ bvLit sym w i
primEval _ _ _ = error "TODO: Add more support in primEval"


bvPrimEval :: (IsSymExprBuilder sym, 1 <= w)
           => sym
           -> NatRepr w
           -> Value
           -> LStateM sym (SymExpr sym (BaseBVType w))
bvPrimEval sym w v = primEval sym (BaseBVRepr w) v

assign2SMT :: IsSymExprBuilder sym => sym -> Ident -> Instr -> LStateM sym ()
assign2SMT sym ident (Arith op (Typed lty lhs) rhs) = do
  case asBaseType lty of
    Just (Some (BaseBVRepr w)) -> do
      lhsv   <- bvPrimEval sym w lhs
      rhsv   <- bvPrimEval sym w rhs
      resv <- io $ arithOpFunc sym op lhsv rhsv
      localsUpdate ident resv
    _ -> error $ "Unsupported type " ++ show lty
assign2SMT sym ident (ICmp op (Typed lty lhs) rhs) = do
  case asBaseType lty of
    Just (Some (BaseBVRepr w)) -> do
      lhsv <- bvPrimEval sym w lhs
      rhsv <- bvPrimEval sym w rhs
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
assign2SMT sym name allocaVal@(Alloca _ty _n _align) = do
  addr <- stackAlloc sym name allocaVal
  addEvent $ AllocaEvent allocaVal name addr
  localsUpdate name addr
assign2SMT sym ident (Load (Typed lty src) _ord _align) = do
  -- TODO: now assume all ptrs are on stack, maybe add a predicate
  mem <- gets heap
  ptr <- primEval sym bv64 src
  Some val <- readMem sym mem ptr lty
  localsUpdate ident val
assign2SMT sym ident@(Ident nm) (Call _tail retty f args) = do
  -- TODO: Add function called to invoke event.
  fPtrVal <- primEval sym bv64 f
  let evalArg (Typed lty av) =
        case asBaseType lty of
          Just (Some tp) ->
            Some <$> primEval sym tp av
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
assign2SMT _ _ instr  = do
  error $ "assign2SMT: unsupported instruction: " ++ show instr

effect2SMT :: (HasCallStack, IsSymExprBuilder sym) => sym -> Instr -> LStateM sym ()
effect2SMT sym instr =
  case instr of
    Store (Typed _ty1 llvmVal) (Typed llvmTy llvmPtr) _align -> do
      case asBaseType llvmTy of
        Nothing -> do
          error $ "Unsupported type " ++ show llvmTy
        Just (Some tp) -> do
          val <- primEval sym tp llvmVal
          ptr <- primEval sym bv64 llvmPtr
          s <- get
          newMem <- writeMem sym (heap s) ptr val
          put $! s { heap = newMem }
    Br (Typed _ty cnd) t1 t2 -> do
      cndv <- primEval sym BaseBoolRepr cnd
      addEvent $ BranchEvent cndv t1 t2
    Jump t -> do
      addEvent $ JumpEvent t
    Ret (Typed llvmTy v) -> do
      case asBaseType llvmTy of
        Just (Some tp) -> do
          val <- primEval sym tp v
          addEvent $ ReturnEvent $ Just $ Some val
        Nothing -> do
          error $ "Unsupported type " ++ show llvmTy
    RetVoid ->
      addEvent $ ReturnEvent Nothing
    _ -> error "Unsupported instruction."

stmt2SMT :: IsSymExprBuilder sym => sym -> Stmt -> LStateM sym ()
stmt2SMT sym (Result ident inst _mds) = do
  -- io $ putStrLn $ show inst
  assign2SMT sym ident inst
stmt2SMT sym (Effect instr _mds) = do
  -- io $ putStrLn $ show inst
  effect2SMT sym instr

bb2SMT :: IsSymExprBuilder sym => sym -> BasicBlock -> LStateM sym ()
bb2SMT sym bb = do
  let ?config = Config True True True
  io $ putStrLn $ show $ ppBasicBlock bb
  forM_ (bbStmts bb) $ stmt2SMT sym

blocks2SMT :: forall sym
           . IsSymExprBuilder sym => sym -> String -> [BasicBlock] -> LStateM sym ()
blocks2SMT sym startBlk bbs = do
  let loop :: BasicBlock -> LStateM sym ()
      loop bb = do
        bb2SMT sym bb
        case brTargets bb of
          [] ->
            pure ()
          [next] ->
            loop $ findBlock next bbs
          _ -> do
            liftIO $ llvmWarning "non-deterministic LLVM branching targets, abort."
  loop $ findBlockByName startBlk bbs

findBlock :: BlockLabel -> [BasicBlock] -> BasicBlock
findBlock lab bbs =
  let match bb = bbLabel bb == Just lab
   in case List.find match bbs of
        Nothing -> llvmError ("Can not find block: " ++ (show lab))
        Just bb -> bb

findBlockByName :: String -> [BasicBlock] -> BasicBlock
findBlockByName ident =
  case Read.readMaybe ident of
    Just i -> findBlock $ Anon i
    Nothing -> findBlock $ Named $ Ident ident

llvmError :: String -> a
llvmError msg = error ("[LLVM Error] " ++ msg)

llvmWarning :: String -> IO ()
llvmWarning msg = putStrLn ("[LLVM Warning] " ++ msg)

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
