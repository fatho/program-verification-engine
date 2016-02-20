module WLP.Wlp where

import GCL.AST
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Z3.Monad

type Ref = String
data Val = RefVal Ref
         | IntVal Int
         | BoolVal Bool

--data Relation = Relation Val Operator Val

type Types = Map Variable Type
type Env = Map Variable (Z3 AST)

subst :: (Variable, Expression) -> Expression -> Expression
subst = undefined

getVal :: Expression -> Val
getVal (Ref r) = RefVal r
getVal (IntLit i) = IntVal i
getVal (BoolLit b) = BoolVal b


wlp :: Statement -> Expression -> Expression
wlp Skip q = q
wlp (Assign e) q = foldr subst q e
wlp (Block stmts) q = foldr wlp q stmts
wlp (Assert e) q = BoolOp OpAnd e q
wlp (Assume e) q = BoolOp OpImplies e q
wlp (NDet s t) q = BoolOp OpAnd (wlp s q) (wlp t q)


mkEnv :: Types -> Env
mkEnv = M.mapWithKey fromTypes
  where fromTypes k BoolType = mkFreshBoolVar k
        fromTypes k IntType = mkFreshIntVar k

toZ3 :: Expression -> Env -> Z3 AST
toZ3 (ExpOp op _e1 _e2) env = do
  e1 <- mkExp _e1 env
  e2 <- mkExp _e2 env
  mkOp op e1 e2

mkExp :: Expression -> Env -> Z3 AST
mkExp (Ref n) e = fromJust $ M.lookup n e
mkExp (IntLit n) _ = mkInteger $ toInteger n
mkExp (BoolLit b) _ = mkBool b
mkExp exp@(ExpOp o e1 e2) env = toZ3 exp env

mkOp :: Operator -> AST -> AST -> Z3 AST
mkOp OpPlus v1 v2 = mkAdd [v1, v2]
mkOp OpMinus v1 v2 = mkSub [v1, v2]
mkOp OpImplies v1 v2 = mkImplies v1 v2
mkOp OpAnd v1 v2 = mkAnd [v1, v2]
