{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
module WLP.Wlp where

import           Control.Monad
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Data.Foldable
import           Data.Map             (Map)
import qualified Data.Map             as M
import           Data.Maybe

import qualified GCL.AST              as AST
import           GCL.DSL
import qualified WLP.Prover.Interface           as Prover

import           Control.Lens.Plated

type Predicate = AST.Expression

subst :: [(AST.QVar, AST.Expression)] -> Predicate -> Predicate
subst sub = transform $ \case
  v@(AST.Ref name) -> fromMaybe v (lookup name sub)
  -- we don't need to worry about the binding of "foralls" at this
  -- point since the names have already been made unique
  other           -> other

wlp :: Monad m => Prover.Backend m -> AST.Statement -> Predicate -> m Predicate
wlp backend s q = AST.simplifyExpr <$> go s q where
  go AST.Skip q          = return q
  go (AST.Assign as) q   = return (subst as q)
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
  go (AST.While iv cnd s) q = do
    preInv <- go s iv
    let preserveInv = iv /\ cnd ==> preInv
        postcnd     = iv /\ neg cnd ==> q
        -- pass simplified expression to prover: it's easier to read & debug for humans
        -- (provided there's no error in the simplifier of course)
        theorem     = AST.simplifyExpr (preserveInv /\ postcnd)
    Prover.valid backend theorem >>= \case
      -- if the invariant is preserved and we can prove the post-condition when exiting the loop,
      -- we only require that the invariant holds in the beginning
      True -> return iv
      -- otherwise, we require that loop is never executed in addition to the post-condition
      False -> return (neg cnd /\ q)

---- Z3 ----
{-

type Env = Map (AST.QVar) (Z3 AST)

mkExp :: Predicate -> Env -> Z3 AST
mkExp (AST.Ref n) e = fromJust $ M.lookup n e
mkExp (AST.IntLit n) _ = mkInteger $ toInteger n
mkExp (AST.BoolLit b) _ = mkBool b
mkExp (AST.BinOp op _e1 _e2) env = do
  e1 <- mkExp _e1 env
  e2 <- mkExp _e2 env
  mkOp op e1 e2

mkOp :: AST.Operator -> AST -> AST -> Z3 AST
mkOp AST.OpPlus v1 v2 = mkAdd [v1, v2]
mkOp AST.OpMinus v1 v2 = mkSub [v1, v2]
mkOp AST.OpImplies v1 v2 = mkImplies v1 v2
mkOp AST.OpAnd v1 v2 = mkAnd [v1, v2]
-}
{-

TODO: Separate Prover Backend from WLP transformer (Modularity rules!)

mkRelation :: Relation -> Z3 AST
mkRelation = undefined

mkVal :: Val -> Z3 AST
mkVal = undefined

toZ3 :: Predicate -> Z3 AST
toZ3 ConstT = mkTrue
toZ3 ConstF = mkFalse
toZ3 (Single r) = mkRelation r
toZ3 (Impl p q) = do
  zp <- toZ3 p
  zq <- toZ3 q
  mkImplies zp zq
toZ3 (Conj p q) = do
  zp <- toZ3 p
  zq <- toZ3 q
  mkAnd [zp,zq]

-}
