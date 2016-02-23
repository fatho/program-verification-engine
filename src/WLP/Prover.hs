{-# LANGUAGE LambdaCase #-}
module WLP.Prover where

import qualified GCL.AST as AST

data Backend m = Backend
  { satisfiable :: AST.Expression -> m Bool
  , valid       :: AST.Expression -> m Bool
  }
