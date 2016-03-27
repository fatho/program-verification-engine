{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-| Contains the implementation of the WLP predicate transformer.
-}
module WLP.Wlp
  ( -- * WLP
    WlpConfig (..)
  , InvalidInvariantBehavior (..)
  , WlpResult (..)
  , defaultConfig
  , withProcedures
  , wlp
  , wlpProgram
    -- * Inference
  , InvariantInference
  , InvariantInferenceArgs (..)
  , neverExecuteInference
  , fixpointInference
  , UnrollMode (..)
  , unrollInference
  ) where

import           WLP.Interface

import           Control.Monad.State
import           GHC.Generics (Generic)
import           Control.DeepSeq
import           Data.Foldable
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.Maybe
import           Data.Typeable
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified GCL.AST                      as AST
import           GCL.DSL

-- | the type of an invariant inference algorithm
type InvariantInference m = forall s. InvariantInferenceArgs (StateT s m) -> StateT s m Predicate

-- | Encapsulates the arguments passed to the invariant inference.
data InvariantInferenceArgs m = InvariantInferenceArgs
  { infLoopGuard     :: AST.Expression
    -- ^ loop guard of the while-loop being processed
  , infLoopBody      :: AST.Statement
    -- ^ loop body of the while-loop being processed
  , infLoopInvariant :: Maybe Predicate
    -- ^ invariant of the while-loop being processed, if annotated
  , infWlp           :: AST.Statement -> Predicate -> m Predicate
    -- ^ the callback into the WLP transformer
  , infPostCondition :: Predicate
    -- ^ the post condition that needs to be established
  }
  deriving (Typeable)

-- | Describes the actions that can be taken if the user-supplied invariant turns out to be incorrect.
data InvalidInvariantBehavior
  = Infer        -- ^ infer invariant instead
  | NeverExecute -- ^ require the loop to not be executed
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Typeable)

-- | Encapsulates the configuration for the WLP transformer.
data WlpConfig m = WlpConfig
  { checkInvariantAnnotation :: Bool
    -- ^ controls whether the WLP transformer should check the user supplied invariant for correctness
  , invalidInvariantBehavior :: InvalidInvariantBehavior
    -- ^ describes the action that is taken if the user-supplied invariant turns out to be incorrect
  , alwaysInferInvariant     :: Bool
    -- ^ controls whether the invariant inference should be called for every while-loop, ignoring the annotations
  , invariantInference       :: InvariantInference m
    -- ^ the invariant inference algorithm to be used
  , procedures               :: Map AST.Name AST.Program
    -- ^ the environment of available procedures for program calls
  }
  deriving (Typeable)

-- | The two modes for unrolling inference.
data UnrollMode
  = UnrollAssert -- ^ assert that the loop condition will not hold after the given number of iterations
  | UnrollAssume -- ^ assume that the loop condition will not hold after the given number of iterations
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Typeable)

-- | Defines a conservative default configuration for the WLP transformer.
--
--     * uses the user-provided invariant if supplied
--
--     * always checks user annotated invariant, (requires the loop to never be executed if invalid)
--
--     * does not perform inference (requires the loop to never be executed)
--
defaultConfig :: Monad m => WlpConfig m
defaultConfig = WlpConfig
  { checkInvariantAnnotation = True
  , invalidInvariantBehavior = NeverExecute
  , alwaysInferInvariant     = False
  , invariantInference       = neverExecuteInference
  , procedures               = M.empty
  }

-- | Extend a WLP configuration with procedures
withProcedures :: Monad m => WlpConfig m -> [Either GclError AST.Program] -> WlpConfig m
withProcedures config mbprocs =
  let
    procs = map (\case
      Left err -> error err
      Right p@(AST.Program n _ _ _) -> (n, p)) mbprocs
  in
    config {procedures = M.union (M.fromList procs) (procedures config) }

-- Builds a program fragment from an external program. Some code is generated
-- to handle input and output variables and the body of the program is inlined.
embedProgram :: AST.Program -> [AST.Expression] -> [AST.QVar] -> AST.Statement
embedProgram (AST.Program _ inVars outVars body) args res =
  AST.Var (inVars ++ outVars) $ AST.Block
    [ AST.Assign (zip (map extractVar inVars) args)
    , body
    , AST.Assign (zip res (map (AST.Ref . extractVar) outVars))]
  where
    extractVar (AST.Decl v _) = v

-- | The WLP transformer. It takes a GCL statement and a post-condition and returns the weakest liberal precondition
-- that ensures that the post-condition holds after executing the statement.
wlp :: MonadProver m => WlpConfig m -> AST.Statement -> Predicate -> m Predicate
wlp WlpConfig{..} stmt postcond = evalStateT (go stmt postcond) 0 where
  go AST.Skip q          = return q
  go (AST.Assign alist) q = return (AST.subst alist q)
  go (AST.Block stmts) q = foldrM go q stmts
  go (AST.Assert e) q =  return (e /\ q)
  go (AST.Assume e) q = return (e ==> q)
  go (AST.NDet s t) q = (\x y -> AST.makeQuantifiersUnique $ x /\ y) <$> go s q <*> go t q
  go (AST.Call pname args res) q = do
    p <- case M.lookup pname procedures of
           Nothing -> fail $ "Procedure " ++ pname ++ " not found"
           Just pr -> return pr
    -- make all variables appearing in the program fragment fresh to avoid name
    -- clashes when a program is called multiple times
    freshP <- makeProgramFresh p
    let proc = embedProgram freshP args res
    trace "Generated the following program fragment from external call"
    trace $ show (PP.pretty $ proc)
    go proc q

  go (AST.Var decls s) q = do
    inner <- go s q
    -- only introduce quantifier, if the variable being quantified over is referred to inside
    -- this transformation is only valid if the type we're quantifying over is not empty,
    -- which is given in our case with those trivial types.
    foldrM (\d@(AST.Decl v _) r ->
      if AST.containsVar v inner
        then return (forall d r)
        else return r) inner decls
  -- invariant provided, check it
  go (AST.InvWhile (Just iv) cnd s) q
    | not alwaysInferInvariant && checkInvariantAnnotation = do
        preInv <- go s iv
        let preserveInv = prepare $ iv /\ cnd ==> preInv
            postcnd     = prepare $ iv /\ neg cnd ==> q
            -- pass simplified expression to prover: it's easier to read & debug for humans
            -- (provided there's no error in the simplifier of course)

        trace "trying to prove invariant is preserved"
        preserved <- prove preserveInv
        trace "trying to prove post condition"
        postValid <- prove postcnd
        if preserved && postValid
          then do
            -- if the invariant is preserved and we can prove the post-condition when exiting the loop,
            -- we only require that the invariant holds in the beginning
            trace "invariant valid: choosing invariant as precondition"
            return iv
          -- otherwise, we require that loop is never executed in addition to the post-condition
          else case invalidInvariantBehavior of
            NeverExecute -> do
              trace "invariant invalid: requiring that loop is never executed"
              return (neg cnd /\ q)
            Infer -> do
              trace "invariant invalid: trying to infer an invariant"
              inferInv (Just iv) cnd s q
    | not alwaysInferInvariant && not checkInvariantAnnotation = do
        trace "assuming user-supplied invariant is correct"
        return iv
  -- invariant should be inferred
  go (AST.InvWhile iv cnd s) q = inferInv iv cnd s q

  inferInv iv cnd s q = do
    let args = InvariantInferenceArgs
          { infLoopGuard     = cnd
          , infLoopBody      = s
          , infLoopInvariant = iv
          , infWlp           = go
          , infPostCondition = q
          }
    trace "invoking invariant inference"
    invariantInference args


  prepare = AST.quantifyFree AST.ForAll . AST.makeQuantifiersUnique

-- Recursvely walk down a programs AST and make every variable occurence fresh.
  makeProgramFresh :: MonadState Int m => AST.Program -> m AST.Program
  makeProgramFresh (AST.Program pname inVars outVars body) = do
    freshInVars <- mapM mkFreshVar inVars
    freshOutVars <- mapM mkFreshVar outVars
    let env = M.fromList $ zip (map extractVar $ inVars ++ outVars) (map extractVar $ freshInVars ++ freshOutVars)
    freshBody <- goST env body
    return $ AST.Program pname freshInVars freshOutVars freshBody
    where
      extractVar (AST.Decl v _) = v
      mkFreshVar (AST.Decl (AST.QVar n _ t) ty) = do
        i <- get
        put (i+1)
        return $ (AST.Decl (AST.QVar n i t) ty)
      goST _   AST.Skip = return AST.Skip
      goST env (AST.Assert e) = do
        freshE <- goE env e
        return $ AST.Assert freshE
      goST env (AST.Assume e) = do
        freshE <- goE env e
        return $ AST.Assume freshE
      goST env (AST.Assign b) = do
        newAss <- freshAss b
        return $ AST.Assign newAss
        where
          freshAss [] = return []
          freshAss ((q, e):rest) = do
            let newQ = env M.! q
            newE <- goE env e
            other <- freshAss rest
            return $ (newQ, newE):(other)
      goST env (AST.Block b) = do
        freshB <- mapM (goST env) b
        return $ AST.Block freshB
      goST env (AST.NDet l r) = do
        freshL <- goST env l
        freshR <- goST env r
        return $ AST.NDet freshL freshR
      goST env (AST.InvWhile mbI g b) = do
        freshG <- goE env g
        freshB <- goST env b
        freshI <- mapM (goE env) mbI
        return $ AST.InvWhile freshI freshG freshB
      goST env (AST.Var v s) = do
        freshVars <- mapM mkFreshVar v
        let extEnv = M.fromList $ zip (map extractVar v) (map extractVar freshVars)
        freshB <- goST (env `M.union` extEnv) s
        return $ AST.Var freshVars freshB
      goST env (AST.Call n a r) = do
        freshA <- mapM (goE env) a
        freshR <- mapM (goVar env) r
        return $ AST.Call n freshA freshR

      goVar env qv = case M.lookup qv env of
        Nothing -> fail $ "variable " ++ show qv ++ " not declared"
        Just replace -> return replace

      goE env (AST.Ref q) = AST.Ref <$> goVar env q
      goE env (AST.Index e1 e2) = do
        freshE1 <- goE env e1
        freshE2 <- goE env e2
        return $ AST.Index freshE1 freshE2
      goE env (AST.RepBy e1 e2 e3) = do
        freshE1 <- goE env e1
        freshE2 <- goE env e2
        freshE3 <- goE env e3
        return $ AST.RepBy freshE1 freshE2 freshE3
      goE env (AST.NegExp e) = do
        freshE <- goE env e
        return $ AST.NegExp freshE
      goE env (AST.IfThenElse i t e) = do
        freshI <- goE env i
        freshT <- goE env t
        freshE <- goE env e
        return $ AST.IfThenElse freshI freshT freshE
      goE env (AST.BinOp op e1 e2) = do
        freshE1 <- goE env e1
        freshE2 <- goE env e2
        return $ AST.BinOp op freshE1 freshE2
      goE env (AST.Quantify q dV e) = do
        freshVar <- mkFreshVar dV
        freshE <- goE (M.insert (extractVar dV) (extractVar freshVar) env) e
        return $ AST.Quantify q freshVar freshE
      goE _ other = return other



-- | Returns for every loop an invariant that ensures that the loop is never executed and
-- the post-condition already holds
neverExecuteInference :: Monad m => InvariantInference m
neverExecuteInference InvariantInferenceArgs{..} = return $ neg infLoopGuard /\ infPostCondition

-- | Tries to infer an invariant using fixpoint iteration.
fixpointInference :: MonadProver m
                  => Maybe Int -- ^ the maximum number of fixpoint iterations, or @Nothing@ for no limit
                  -> InvariantInference m
fixpointInference maxIterations InvariantInferenceArgs{..} = run 1 true where
  run i old
    | fmap (i >) maxIterations == Just True = do
        trace "reached limit for fixpoint iteration: requiring that loop is never executed"
        return (neg infLoopGuard /\ infPostCondition)
    | otherwise = do
        trace $ "Fixpoint iter. #" ++ show i
        new <- f old
        prove (AST.quantifyFree AST.ForAll $ AST.makeQuantifiersUnique $ new <=> old) >>= \case
          True -> return old -- reached fixpoint
          False -> run (i+1) new

  f q = do
    w <- infWlp infLoopBody q
    return $ (infLoopGuard /\ w) \/ (neg infLoopGuard /\ infPostCondition)

-- | Tries to infer an invariant by finitely unrolling a loop, with a supplied base case for the last iteration.
unrollInference :: UnrollMode -- ^ controls how to handle the base case
                -> Int -- ^ the number of iterations to be unrolled
                -> InvariantInference m
unrollInference baseCase numUnroll InvariantInferenceArgs{..} = infWlp unrolledLoop infPostCondition where
  unrolledLoop = finiteUnroll baseStmt numUnroll infLoopGuard infLoopBody
  baseStmt cond = case baseCase of
    UnrollAssert -> AST.Assert cond
    UnrollAssume -> AST.Assume cond

-- | Unrolls a given number of iterations of a  while loops and uses the supplied base case.
finiteUnroll :: (Predicate -> AST.Statement) -- ^ the function generating the base case. it receives the negation of the loop guard as argument
            -> Int -- ^ the number of iterations to unroll
            -> Predicate -- ^ the loop guard
            -> AST.Statement -- ^ the loop body
            -> AST.Statement -- ^ the unrolled loop
finiteUnroll baseCase numUnroll loopGuard body = go numUnroll where
  go k
    | k Prelude.<= 0 = baseCase (neg loopGuard)
    | otherwise      = astIf loopGuard (AST.Block [body, go (k-1)]) AST.Skip
  astIf cnd thenB elseB = AST.NDet
    (AST.Block [AST.Assume cnd, thenB])
    (AST.Block [AST.Assume (neg cnd), elseB])

-- | The result from computing the WLP of a program
data WlpResult = WlpResult
  { wlpResultPrecondition   :: Predicate
    -- ^ the weakest liberal precondition that has been computed
  , wlpResultVerified       :: Bool
    -- ^ tells whether the precondition could be verified or not
  , wlpResultCounterExample :: Maybe CounterExample
  } deriving (Generic, NFData)

instance PP.Pretty WlpResult where
  pretty WlpResult{..}
    | wlpResultVerified = template $ PP.green "verified"
    | otherwise         = template $ PP.red "disproved"
    where
      template result = PP.hang 2 $ "derived and" PP.<+> result PP.<+> "precondition: " PP.</> PP.pretty wlpResultPrecondition

-- | Entry point for WLP. Qualifies program input and ouput variables
wlpProgram :: MonadProver m => WlpConfig m -> AST.Program -> m WlpResult
wlpProgram cfg (AST.Program _ i o body) = do
  precond <- wlp cfg (AST.Var (i ++ o) body) true
  trace "proving final precondition"
  ce <- prove' precond
  return $ WlpResult precond (isNothing ce) ce
