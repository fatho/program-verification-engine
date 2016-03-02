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

data Sym = Val SVal | Arr SArr

buildTheorem :: GCL.Expression -> Symbolic Sym
buildTheorem ex = go Map.empty ex where
  go env ex = case ex of
    GCL.IntLit i -> return $ Val $ svInteger KUnbounded (toInteger i)
    GCL.BoolLit b -> return $ Val $ svBool b
    GCL.Ref var -> case Map.lookup var env of
      Nothing -> fail $ "variable " ++ show var ++ " not declared"
      Just sym -> return sym
    GCL.BinOp op l r -> do
      Val lval <- go env l
      Val rval <- go env r
      return $ Val $ symOperator op lval rval
    GCL.Index arr idx -> do
      Arr sArr <- go env arr
      Val sIdx <- go env idx
      return $ Val $ readSArr sArr sIdx
    GCL.RepBy arr idx new -> do
      Arr sArr <- go env arr
      Val sIdx <- go env idx
      Val sNew <- go env new
      return $ Arr $ writeSArr sArr sIdx sNew
    GCL.NegExp ex -> do
      Val nVal <- go env ex
      return $ Val $ svNot nVal
    GCL.ForAll (GCL.Decl var ty) ex -> do
      case ty of
        GCL.BasicType ty -> do
          let kind = kindOfType ty
              name = qvarString var
          svar <- svMkSymVar (Just ALL) kind (Just name)
          go (Map.insert var (Val svar) env) ex
        GCL.ArrayType ty -> do
          let kind = kindOfType ty
          sarr <- newSArr (KUnbounded, kind) (const $ qvarString var) Nothing
          go (Map.insert var (Arr sarr) env) ex

sbv :: SMTConfig -> Backend IO
sbv satCfg = Backend
  { valid = \ex -> do
      let thm = getVal $ buildTheorem ex
      result <- proveWith satCfg thm
      print result
      return $ not $ Z3.modelExists result
  , satisfiable = \ex -> do
      let thm = getVal $ buildTheorem ex
      result <- satWith satCfg thm
      print result
      return $ Z3.modelExists result
  } where
    getVal :: Symbolic Sym -> Symbolic SVal
    getVal symV = do
      Val v <- symV
      return v

z3 = sbv Z3.sbvCurrentSolver
