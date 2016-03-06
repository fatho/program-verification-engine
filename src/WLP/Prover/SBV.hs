{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RecordWildCards #-}
{-| Defines an interpreter for the 'WLP.Interface.WLP' free monad using "Data.SBV" as a backend for theorem proving.
-}
module WLP.Prover.SBV
  ( -- * Interface
    interpretSBV
  , parInterpretSBV
  ) where

import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.IO.Class
import           Control.Concurrent.Async
import           Data.List              (intercalate)
import qualified Data.Map.Strict        as Map
import qualified Data.SBV.Bridge.Z3     as Z3
import           Data.SBV.Dynamic

import qualified GCL.AST                as GCL
import           WLP.Interface

-- | Generates an SBV name for a 'QVar'.
qvarString :: GCL.QVar -> String
qvarString (GCL.QVar names uid _) = intercalate "_" names ++ "_" ++ show uid

-- | Translates an operator to SBV.
symOperator :: GCL.Operator -> SVal -> SVal -> SVal
symOperator GCL.OpLEQ = svLessEq
symOperator GCL.OpEQ = svEqual
symOperator GCL.OpGEQ = svGreaterEq
symOperator GCL.OpLT = svLessThan
symOperator GCL.OpGT = svGreaterThan
symOperator GCL.OpPlus = svPlus
symOperator GCL.OpMinus = svMinus
symOperator GCL.OpTimes = svTimes
symOperator GCL.OpImplies = \a b -> svOr (svNot a) b
symOperator GCL.OpIff = \a b -> svOr (svAnd a b) (svAnd (svNot a) (svNot b))
symOperator GCL.OpAnd = svAnd
symOperator GCL.OpOr = svOr

-- | Returns the SBV kind corresponding to a GCL type.
kindOfType :: GCL.PrimitiveType -> Kind
kindOfType GCL.IntType = KUnbounded
kindOfType GCL.BoolType = KBool

-- | A symbolic value
data Sym
  = Val SVal
    -- ^ symbolic primitive value
  | Arr SArr
    -- ^ symbolic array

-- | Asserts that we got an 'SVal' inside a 'Sym'.
requireVal :: Monad m => m Sym -> m SVal
requireVal symV = do
  Val v <- symV
  return v

-- | Builds an SBV theorem from a (boolean) GCL expression. Type correctness is not checked.
buildTheorem :: GCL.Expression -> Symbolic Sym
buildTheorem = go Map.empty where
  go env expr = case expr of
    GCL.IntLit i -> return $ Val $ svInteger KUnbounded (toInteger i)
    GCL.BoolLit b -> return $ Val $ svBool b
    GCL.Ref var -> case Map.lookup var env of
      Nothing -> fail $ "variable " ++ show var ++ " not declared"
      Just sym -> return sym
    GCL.BinOp op l r -> do
      Val lval <- go env l
      Val rval <- go env r
      return $ Val $ symOperator op lval rval
    GCL.Index arr idx -> do
      Arr sArr <- go env arr
      Val sIdx <- go env idx
      return $ Val $ readSArr sArr sIdx
    GCL.RepBy arr idx new -> do
      Arr sArr <- go env arr
      Val sIdx <- go env idx
      Val sNew <- go env new
      return $ Arr $ writeSArr sArr sIdx sNew
    GCL.NegExp ex -> do
      Val nVal <- go env ex
      return $ Val $ svNot nVal
    GCL.ForAll (GCL.Decl var varTy) ex -> do
      case varTy of
        GCL.BasicType ty -> do
          let kind = kindOfType ty
              name = qvarString var
          svar <- svMkSymVar (Just ALL) kind (Just name)
          go (Map.insert var (Val svar) env) ex
        GCL.ArrayType ty -> do
          let kind = kindOfType ty
          sarr <- newSArr (KUnbounded, kind) (const $ qvarString var) Nothing
          go (Map.insert var (Arr sarr) env) ex
    GCL.IfThenElse cond tval fval -> do
      Val c <- go env cond
      Val t <- go env tval
      Val f <- go env fval
      return $ Val $ svIte c t f

-- | The free monad interpreter using SBV.
interpretSBV :: MonadIO m
             => SMTConfig           -- ^ the configuration telling SBV what prover it should use
             -> OutputMode          -- ^ controls the verbosity of the computation
             -> (Predicate -> m ()) -- ^ a function to trace a predicate (used in 'TraceMode')
             -> WLP a               -- ^ the WLP computation
             -> m a
interpretSBV smt outputMode tracePredicate = iterM run where
  run (Prove predi cont) = do
    let thm = requireVal $ buildTheorem predi
    runIfTrace (tracePredicate predi)
    result <- liftIO $ proveWith smt thm
    runIfTrace (liftIO $ print result)
    cont (not $ Z3.modelExists result)

  run (Trace msg cont) = do
    runIfTrace $ liftIO $ putStrLn msg
    cont

  runIfTrace :: Monad m => m () -> m ()
  runIfTrace = when (outputMode == TraceMode)


parInterpretSBV :: SMTConfig -> WLP a -> IO a
parInterpretSBV smt = iterM run where
  run (Prove predi cont) = do
    let thm = requireVal $ buildTheorem predi

    tCont <- async $ cont True
    fCont <- async $ cont False

    withAsync (proveWith smt thm) $ \result -> do
      res <- wait result
      pickCont (not $ Z3.modelExists res) tCont fCont

  run (Trace _ cont) = cont

  pickCont :: Bool -> Async a -> Async a -> IO a
  pickCont True a b = do
    cancel b
    wait a
  pickCont False a b = do
    cancel a
    wait b
