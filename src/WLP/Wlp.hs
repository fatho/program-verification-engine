{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE OverloadedStrings          #-}
module WLP.Wlp where

import           WLP.Interface

import           Data.Foldable
import           Data.Maybe
import           Data.Set                     (Set)
import qualified Data.Set                     as S
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified GCL.AST                      as AST
import           GCL.DSL

import           Control.Lens.Plated

subst :: [(AST.QVar, AST.Expression)] -> Predicate -> Predicate
subst sub = transform $ \case
  v@(AST.Ref name) -> fromMaybe v (lookup name sub)
  -- we don't need to worry about the binding of "foralls" at this
  -- point since the names have already been made unique
  other           -> other

freeVariables :: Predicate -> Set AST.QVar
freeVariables = para go where
  go (AST.Ref qv) = S.insert qv . S.unions
  go (AST.ForAll (AST.Decl v _) _) = S.delete v . S.unions
  go _            = S.unions

quantifyFree :: Predicate -> Predicate
quantifyFree p = foldr quantify p (freeVariables p) where
  quantify qv@(AST.QVar _ _ ty) inner = AST.ForAll (AST.Decl qv ty) inner

wlp :: MonadProver m => AST.Statement -> Predicate -> m Predicate
wlp stmt postcond = go stmt postcond where
  go AST.Skip q          = return q
  go (AST.Assign alist) q   = return (subst alist q)
  go (AST.Block stmts) q = foldrM go q stmts
  go (AST.Assert e) q =  return (e /\ q)
  go (AST.Assume e) q = return (e ==> q)
  go (AST.NDet s t) q = (/\) <$> go s q <*> go t q
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
  go (AST.InvWhile (Just iv) cnd s) q = do
    preInv <- go s iv
    let preserveInv = iv /\ cnd ==> preInv
        postcnd     = iv /\ neg cnd ==> q
        -- pass simplified expression to prover: it's easier to read & debug for humans
        -- (provided there's no error in the simplifier of course)
        theorem     = quantifyFree (preserveInv /\ postcnd)

    trace "Trying to prove invariant is preserved"
    prove theorem >>= \case
      -- if the invariant is preserved and we can prove the post-condition when exiting the loop,
      -- we only require that the invariant holds in the beginning
      True -> do
        trace "Choosing invariant as precondition"
        return iv
      -- otherwise, we require that loop is never executed in addition to the post-condition
      False -> do
        trace "Requiring that loop is never executed"
        return (neg cnd /\ q)
  -- invariant not provided
  go (AST.InvWhile Nothing cnd s) q = do
    --trace "cannot infer invariant yet, requiring that loop is never executed"
    --return (neg cnd /\ q)
    trace "Trying to compute fixpoint of loop precondition"
    fixpointWhile 5 cnd s q

fixpointWhile :: MonadProver m => Int -> Predicate -> AST.Statement -> Predicate -> m Predicate
fixpointWhile maxIterations loopCnd loopBody postCnd = run maxIterations true where
  run i old
    | i <= 0 = do
        trace "reached limit for fixpoint iteration, requiring that loop is never executed"
        return (neg loopCnd /\ postCnd)
    | otherwise = do
        trace $ "Fixpoint iter. #" ++ show (maxIterations - i + 1)
        new <- f old
        prove (quantifyFree $ new <=> old) >>= \case
          True -> return old -- reached fixpoint
          False -> run (i-1) new

  f q = do
    w <- wlp loopBody q
    return $ (loopCnd /\ w) \/ (neg loopCnd /\ postCnd)

finiteUnroll :: (Predicate -> AST.Statement) -> Int -> Predicate -> AST.Statement -> AST.Statement
finiteUnroll baseCase numUnroll loopGuard body = go numUnroll where
  go k
    | k Prelude.<= 0 = baseCase (neg loopGuard)
    | otherwise      = astIf loopGuard (AST.Block [body, go (k-1)]) AST.Skip
  astIf cnd thenB elseB = AST.NDet
    (AST.Block [AST.Assume cnd, thenB])
    (AST.Block [AST.Assume (neg cnd), elseB])

data WlpResult
  = Verified Predicate
  | Disproved Predicate
  deriving (Show, Eq, Ord)

instance PP.Pretty WlpResult where
  pretty (Verified predi) = PP.hang 2 $ "Derived and verified precondition: " PP.</> PP.pretty predi
  pretty (Disproved predi) = PP.hang 2 $ "Derived but disproved precondition: " PP.</> PP.pretty predi

precondition :: WlpResult -> Predicate
precondition (Verified p) = p
precondition (Disproved p) = p

-- | Entry point for WLP. Qualifies program input and ouput variables
wlpProgram :: MonadProver m => AST.Program -> m WlpResult
wlpProgram (AST.Program _ i o body) = do
  precond <- wlp (AST.Var (i ++ o) body) true
  trace "Proving final precondition"
  prove precond >>= \case
    True -> return $ Verified precond
    False -> return $ Disproved precond
