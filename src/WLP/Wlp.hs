{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
module WLP.Wlp where

import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.Reader
import           Control.Monad.Writer
import           Data.Foldable
import           Data.Map                     (Map)
import qualified Data.Map                     as M
import           Data.Maybe
import           Data.Set                     (Set)
import qualified Data.Set                     as S

import qualified GCL.AST                      as AST
import           GCL.DSL
import qualified WLP.Prover.Interface         as Prover

import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

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

-- | Entry point for WLP. Qualifies program input and ouput variables
wlpProgram :: AST.Program -> Predicate
wlpProgram (AST.Program _ i o body) =
  wlp (AST.Var (i ++ o) body) true

freeVariables :: Predicate -> Set AST.QVar
freeVariables = para go where
  go (AST.Ref qv) = S.insert qv . S.unions
  go (AST.ForAll (AST.Decl v _) _) = S.delete v . S.unions
  go _            = S.unions

quantifyFree :: Predicate -> Predicate
quantifyFree p = foldr quantify p (freeVariables p) where
  quantify qv@(AST.QVar _ _ ty) inner = AST.ForAll (AST.Decl qv ty) inner

prettyPrint :: PP.Pretty a => Int -> a -> IO ()
prettyPrint width = PP.displayIO stdout . PP.renderPretty 0.8 width . PP.pretty

wlpMonadic :: MonadIO m => Prover.Backend m -> AST.Statement -> Predicate -> m Predicate
wlpMonadic backend s q = AST.simplifyExpr <$> go s q where
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
        theorem     = quantifyFree (preserveInv /\ postcnd)
    liftIO $ do
      putStrLn "Trying to prove invariant is preserved"
      prettyPrint 100 (PP.indent 2 (PP.pretty theorem PP.<> PP.linebreak))
    Prover.valid backend theorem >>= \case
      -- if the invariant is preserved and we can prove the post-condition when exiting the loop,
      -- we only require that the invariant holds in the beginning
      True -> do
        liftIO $ putStrLn "Choosing invariant as precondition"
        return iv
      -- otherwise, we require that loop is never executed in addition to the post-condition
      False -> do
        liftIO $ putStrLn "Requiring that loop is never executed"
        return (neg cnd /\ q)

-- | Entry point for WLP. Qualifies program input and ouput variables
wlpProgramMonadic :: MonadIO m => Prover.Backend m -> AST.Program -> m Predicate
wlpProgramMonadic backend (AST.Program _ i o body) =
  wlpMonadic backend (AST.Var (i ++ o) body) true
