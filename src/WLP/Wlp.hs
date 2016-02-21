{-# LANGUAGE LambdaCase #-}
module WLP.Wlp where

import GCL.AST
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Z3.Monad



subst :: (QVar, Expression) -> Expression -> Expression
subst = undefined

wlp :: Statement -> Expression -> Expression
wlp Skip q = q
wlp (Assign e) q = foldr subst q e
wlp (Block stmts) q = foldr wlp q stmts
wlp (Assert e) q = BinOp OpAnd e q
wlp (Assume e) q = BinOp OpImplies e q
wlp (NDet s t) q = BinOp OpAnd (wlp s q) (wlp t q)

---- Z3 ----


type Env = Map QVar (Z3 AST)

mkExp :: Expression -> Env -> Z3 AST
mkExp (Ref n) e = fromJust $ M.lookup n e
mkExp (IntLit n) _ = mkInteger $ toInteger n
mkExp (BoolLit b) _ = mkBool b
mkExp (BinOp op _e1 _e2) env = do
  e1 <- mkExp _e1 env
  e2 <- mkExp _e2 env
  mkOp op e1 e2

mkOp :: Operator -> AST -> AST -> Z3 AST
mkOp OpPlus v1 v2 = mkAdd [v1, v2]
mkOp OpMinus v1 v2 = mkSub [v1, v2]
mkOp OpImplies v1 v2 = mkImplies v1 v2
mkOp OpAnd v1 v2 = mkAnd [v1, v2]

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
