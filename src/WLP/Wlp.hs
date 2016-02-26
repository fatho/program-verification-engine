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
import qualified WLP.Prover.Interface as Prover

import           Control.Lens.Plated

type Predicate = AST.Expression

subst :: [(AST.QVar, AST.Expression)] -> Predicate -> Predicate
subst sub = transform $ \case
  v@(AST.Ref name) -> fromMaybe v (lookup name sub)
  -- we don't need to worry about the binding of "foralls" at this
  -- point since the names have already been made unique
  other           -> other

wlp :: AST.Statement -> Predicate -> Predicate
wlp s q = AST.simplifyExpr $ go s q where
  go AST.Skip q          = q
  go (AST.Assign as) q   = subst as q
  go (AST.Block stmts) q = foldr go q stmts
  go (AST.Assert e) q =  e /\ q
  go (AST.Assume e) q = e ==> q
  go (AST.NDet s t) q = go s q /\ go t q
  go (AST.Var decls s) q = foldr forall (go s q) decls
  go (AST.While iv cnd s) q =
    let preserveInv = iv /\ cnd ==> go s iv
        postcnd     = iv /\ neg cnd ==> q
        preserved   = preserveInv /\ postcnd
    in (preserved ==> iv) /\ (neg preserved ==> (neg cnd /\ q))

wlpProgram :: AST.Program -> Predicate
wlpProgram (AST.Program _ i o body) =
  wlp (AST.Var (i ++ o) body) true
