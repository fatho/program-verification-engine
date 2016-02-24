{-# LANGUAGE RankNTypes #-}
module WLP.Prover.SBV where

import           WLP.Prover.Interface

import qualified GCL.AST              as GCL

import qualified Data.SBV             as SBV
import qualified Data.SBV.Bridge.Z3   as Z3

buildTheorem :: GCL.Expression -> SBV.Predicate
buildTheorem = undefined

sbv :: (forall a. SBV.Provable a => a -> IO SBV.ThmResult)
    -> (forall a. SBV.Provable a => a -> IO SBV.SatResult)
    -> Backend IO
sbv proveThm sat = Backend
  { valid = undefined -- .... proveThm ...
  , satisfiable = undefined -- ... sat ....
  }
