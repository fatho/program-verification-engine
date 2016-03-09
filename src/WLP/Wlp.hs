{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RecordWildCards            #-}
{-| Contains the implementation of the WLP predicate transformer.
-}
module WLP.Wlp
  ( -- * WLP
    WlpConfig (..)
  , InvalidInvariantBehavior (..)
  , WlpResult (..)
  , defaultConfig
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

import           Data.Foldable
import           Data.Typeable
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map                     as M

import qualified GCL.AST                      as AST
import           GCL.DSL

-- | the type of an invariant inference algorithm
type InvariantInference m = InvariantInferenceArgs m -> m Predicate

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

data ExternalProgram =
    Explicit AST.Program
  | Implicit ProgramSpec

data ProgramSpec = ProgramSpec
  { preConditions       :: AST.Expression
  , postConditions      :: AST.Expression
  , inVar               :: [AST.Decl AST.QVar]
  , outVar              :: [AST.Decl AST.QVar]
  } deriving (Typeable)

data AbstractProgram = AbstractProgram
  { varIn               :: [AST.Decl AST.QVar]
  , varOut              :: [AST.Decl AST.QVar]
  , body                :: AST.Statement
  }

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
  , procedures               :: Map AST.Name ExternalProgram
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

-- incProc :: ProgramSpec
-- incProc = ProgramSpec {
--     inVar = ["r"]
--   , outVar = ["r"]
--   , preConditions = "r" .== 0
--   , postConditions = "r" .== 1
-- }

toAbstractP :: ExternalProgram -> AbstractProgram
toAbstractP (Explicit (AST.Program _ i o b)) = AbstractProgram i o b
toAbstractP (Implicit ProgramSpec{..}) =
  let body = AST.Block [AST.Assert preConditions, AST.Assume postConditions]
  in AbstractProgram inVar outVar body


buildConcrete :: AbstractProgram -> [AST.Expression] -> [AST.Expression] -> AST.Statement
buildConcrete AbstractProgram{..} args res =
  AST.Var (varIn ++ varOut) $ AST.Block
    [ AST.Assign (zip (map extractVars varIn) args)
    , body
    , AST.Assign (zip (map extractVars varOut) res)]
  where extractVars (AST.Decl v _) = v

-- | The WLP transformer. It takes a GCL statement and a post-condition and returns the weakest liberal precondition
-- that ensures that the post-condition holds after executing the statement.
wlp :: MonadProver m => WlpConfig m -> AST.Statement -> Predicate -> m Predicate
wlp config@WlpConfig{..} stmt postcond = go stmt postcond where
  go AST.Skip q          = return q
  go (AST.Assign alist) q = return (AST.subst alist q)
  go (AST.Block stmts) q = foldrM go q stmts
  go (AST.Assert e) q =  return (e /\ q)
  go (AST.Assume e) q = return (e ==> q)
  go (AST.NDet s t) q = (/\) <$> go s q <*> go t q
  go (AST.Call prog args res) q = do
    let abstractP = toAbstractP $ fromJust $ M.lookup prog procedures
    let concreteP = buildConcrete abstractP args res
    wlp config concreteP q

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
        let preserveInv = iv /\ cnd ==> preInv
            postcnd     = iv /\ neg cnd ==> q
            -- pass simplified expression to prover: it's easier to read & debug for humans
            -- (provided there's no error in the simplifier of course)
            theorem     = AST.quantifyFree (preserveInv /\ postcnd)

        trace "trying to prove invariant is preserved"
        prove theorem >>= \case
          -- if the invariant is preserved and we can prove the post-condition when exiting the loop,
          -- we only require that the invariant holds in the beginning
          True -> do
            trace "invariant valid: choosing invariant as precondition"
            return iv
          -- otherwise, we require that loop is never executed in addition to the post-condition
          False -> case invalidInvariantBehavior of
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
        prove (AST.quantifyFree $ new <=> old) >>= \case
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

-- | Unrolls a given number of iterations of a  while loop and uses the supplied base case.
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
  { wlpResultPrecondition :: Predicate
    -- ^ the weakest liberal precondition that has been computed
  , wlpResultVerified     :: Bool
    -- ^ tells whether the precondition could be verified or not
  }

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
  valid <- prove precond
  return $ WlpResult precond valid
