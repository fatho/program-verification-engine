{-# LANGUAGE LambdaCase #-}
module WLP.Wlp where

import qualified GCL.AST             as AST
import qualified GCL.DSL             as DSL

import           Control.Lens.Plated
import           Data.Map.Strict     (Map)
import qualified Data.Map.Strict     as Map
import           Data.Maybe

-- TODO: Maybe we need another representation for this
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
wlp (AST.Assert e) q = e DSL.&& q
wlp (AST.Assume e) q = e DSL.==> q
wlp (AST.NDet s t) q = wlp s q DSL.&& wlp t q

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
