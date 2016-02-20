module WLP.Wlp where

import qualified GCL.AST  as AST

import           Data.Map (Map)
import qualified Data.Map as M
import           Z3.Monad

-- TODO: Maybe we need another representation for this
type Predicate = AST.Expression

subst :: AST.QualifiedVar -> AST.Expression -> Predicate -> Predicate
subst = undefined

(.&.) :: Predicate -> Predicate -> Predicate
(.&.) = AST.BoolOp AST.OpAnd

(==>) :: Predicate -> Predicate -> Predicate
(==>) = AST.BoolOp AST.OpImplies

wlp :: AST.Statement -> Predicate -> Predicate
wlp AST.Skip q = q
wlp (AST.Assign as) q = undefined
wlp (AST.Block stmts) q = foldr wlp q stmts
wlp (AST.Assert e) q = e .&. q
wlp (AST.Assume e) q = e ==> q
wlp (AST.NDet s t) q = wlp s q .&. wlp t q

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
