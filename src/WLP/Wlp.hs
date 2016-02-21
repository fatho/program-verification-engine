{-# LANGUAGE LambdaCase #-}
module WLP.Wlp where

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Z3.Monad

import qualified GCL.AST             as AST
import qualified GCL.DSL             as DSL

import           Control.Lens.Plated

type Predicate = AST.Expression

subst :: [(AST.QVar, AST.Expression)] -> Predicate -> Predicate
subst sub = transform $ \case
  v@(AST.Ref name) -> fromMaybe v (lookup name sub)
  -- we don't need to worry about the binding of "foralls" at this
  -- point since the names have already been made unique
  other           -> other


wlp :: AST.Statement -> Predicate -> Predicate
wlp AST.Skip q = q
wlp (AST.Assign as) q = subst as q
wlp (AST.Block stmts) q = foldr wlp q stmts
wlp (AST.Assert e) q =  e DSL.&& q
wlp (AST.Assume e) q = e DSL.==> q
wlp (AST.NDet s t) q = wlp s q DSL.&& wlp t q


---- Z3 ----


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
