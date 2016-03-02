{-# LANGUAGE RankNTypes #-}
module WLP.Prover.SBV where

import           WLP.Prover.Interface

import           Data.List            (intercalate)
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as Map
import qualified Data.SBV.Bridge.Z3   as Z3
import           Data.SBV.Dynamic
import qualified GCL.AST              as GCL

import           Debug.Trace

qvarString :: GCL.QVar -> String
qvarString (GCL.QVar names id _) = intercalate "_" names ++ "_" ++ show id

symOperator :: GCL.Operator -> SVal -> SVal -> SVal
symOperator GCL.OpLEQ = svLessEq
symOperator GCL.OpEQ = svEqual
symOperator GCL.OpGEQ = svGreaterEq
symOperator GCL.OpLT = svLessThan
symOperator GCL.OpGT = svGreaterThan
symOperator GCL.OpPlus = svPlus
symOperator GCL.OpMinus = svMinus
symOperator GCL.OpTimes = svTimes
symOperator GCL.OpImplies = \a b -> svOr (svNot a) b
symOperator GCL.OpAnd = svAnd
symOperator GCL.OpOr = svOr

kindOfType :: GCL.PrimitiveType -> Kind
kindOfType GCL.IntType = KUnbounded
kindOfType GCL.BoolType = KBool

buildTheorem :: GCL.Expression -> Symbolic SVal
buildTheorem ex = go Map.empty ex where
  go env ex = case ex of
    GCL.IntLit i -> return $ svInteger KUnbounded (toInteger i)
    GCL.BoolLit b -> return $ svBool b
    GCL.Ref var -> case Map.lookup var env of
      Nothing -> fail $ "variable " ++ show var ++ " not declared"
      Just sv -> return sv
    GCL.BinOp op l r -> symOperator op <$> go env l <*> go env r
    GCL.Index arr idx -> undefined
    GCL.RepBy arr idx new -> undefined
    GCL.NegExp ex -> svNot <$> go env ex
    GCL.ForAll (GCL.Decl var ty) ex -> do
      case ty of
        GCL.BasicType ty -> do
          let kind = kindOfType ty
              name = qvarString var
          svar <- svMkSymVar (Just ALL) kind (Just name)
          go (Map.insert var svar env) ex
        GCL.ArrayType ty -> do
          return undefined

--buildTheorem = undefined

sbv :: SMTConfig -> Backend IO
sbv satCfg = Backend
  { valid = \ex -> do
      let thm = buildTheorem ex
      result <- proveWith satCfg thm
      print result
      return $ not $ Z3.modelExists result
  , satisfiable = \ex -> do
      let thm = buildTheorem ex
      result <- satWith satCfg thm
      print result
      return $ Z3.modelExists result
  }

z3 = sbv Z3.sbvCurrentSolver
