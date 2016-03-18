{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo     #-}
{-| Defines an interpreter for the 'WLP.Interface.WLP' free monad using "Data.SBV" as a backend for theorem proving.
-}
module WLP.Prover.SBV
  ( -- * Interface
    interpretSBV
  , parInterpretSBV
  ) where

import           Control.Concurrent.Async
import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.IO.Class
import           Data.List                (intercalate, sortOn)
import qualified Data.Map.Strict          as Map
import           Data.Maybe
import qualified Data.SBV.Bridge.Z3       as Z3
import           Data.SBV.Dynamic

import qualified GCL.AST                  as GCL
import           WLP.Interface

import           Debug.Trace

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

-- | Converts a formula to prenex normal form and separates it into a list of quantified variables and
-- a quantifier-free expression
separateQuantifiers :: GCL.Expression -> ([(GCL.Quantifier, GCL.QVar)], GCL.Expression)
separateQuantifiers expr = go [] (GCL.prenex expr) where
  go vars expr = case expr of
    GCL.Quantify quantifier (GCL.Decl var varTy) ex -> go ((quantifier, var) : vars) ex
    other -> (vars, other)

-- | Builds an SBV theorem from a (boolean) GCL expression. Type correctness is not checked.
buildTheorem :: [(GCL.Quantifier, GCL.QVar)] -> GCL.Expression -> Symbolic Sym
buildTheorem vars expr = build where
  build = do
    varMap <- mapM (uncurry declVar) sortedVars
    go (Map.fromList varMap) expr

  sortedVars = sortOn fst vars

  declVar quantifier var@(GCL.QVar _ _ varTy) =
    case varTy of
      GCL.BasicType ty -> do
        let kind = kindOfType ty
            name = qvarString var
            sbvQ = case quantifier of
                     GCL.ForAll -> ALL
                     GCL.Exists -> EX
        svar <- svMkSymVar (Just sbvQ) kind (Just name)
        return (var, Val svar)
      GCL.ArrayType ty -> do
        let kind = kindOfType ty
            --initVal = case ty of
            --  GCL.BoolType -> svFalse
            --  GCL.IntType -> svInteger KUnbounded 0
        when (quantifier == GCL.Exists) $ fail "existential array quantification not supported by backend"
        sarr <- newSArr (KUnbounded, kind) (const $ qvarString var) Nothing
        return (var, Arr sarr)

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
    GCL.Quantify quantifier (GCL.Decl var varTy) ex ->
      fail $ "error: nested quantifiers should have been moved to front by conversion to prenex normal form"
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
    let (vars,quantFree) = separateQuantifiers $ GCL.prenex $ predi
        thm = requireVal $ buildTheorem vars quantFree
    runIfTrace $ do
      liftIO $ putStrLn "Input formula:"
      tracePredicate predi
      liftIO $ do
        putStrLn "Quantifier free form:"
        print vars
      tracePredicate quantFree
    result <- liftIO $ proveWith smt thm
    runIfTrace (liftIO $ print result)
    --cont (not $ Z3.modelExists result)
    if Z3.modelExists result
      then cont $ Just $ fmap show $ Z3.getModelDictionary result
      else cont Nothing

  run (Trace msg cont) = do
    runIfTrace $ liftIO $ putStrLn msg
    cont

  runIfTrace :: Monad m => m () -> m ()
  runIfTrace = when (outputMode == TraceMode)

parInterpretSBV :: SMTConfig -> WLP a -> IO a
parInterpretSBV smt = iterM run where
  run (Prove predi cont) = mdo
    let (vars,quantFree) = separateQuantifiers $ GCL.prenex $ predi
        thm = requireVal $ buildTheorem vars quantFree

    tCont <- async $ liftIO $ cont Nothing
    fCont <- async $ liftIO $ cont (Just $ fmap show $ Z3.getModelDictionary res)

    res <- liftIO $ proveWith smt thm
    pickCont (not $ Z3.modelExists res) tCont fCont

  run (Trace _ cont) = cont

  pickCont :: Bool -> Async a -> Async a -> IO a
  pickCont True a b = do
    cancel b
    wait a
  pickCont False a b = do
    cancel a
    wait b
