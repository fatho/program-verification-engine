module WLP.Wlp where

import GCL.AST
import Data.Map (Map)
import qualified Data.Map as M
import Z3.Monad

type Ref = String
data Val = RefVal Ref
         | IntVal Int
         | BoolVal Bool

data Relation = Relation Val Operator Val
data Predicate = ConstT
               | ConstF
               | Single Relation
               | Impl Predicate Predicate
               | Conj Predicate Predicate

subst :: Expression -> Target -> Predicate -> Predicate
subst = undefined

toPred :: Expression -> Predicate
toPred (BinaryOp e1 o e2) = let
  v1 = getVal e1
  v2 = getVal e2
  in Single $ Relation v1 o v2

getVal :: Expression -> Val
getVal (Ref r) = RefVal r
getVal (IntLit i) = IntVal i
getVal (BoolLit b) = BoolVal b

(<^>), (<=>>) :: Predicate -> Predicate -> Predicate
(<^>) p q = Conj p q
(<=>>) p q = Impl p q

wlp :: Statement -> Predicate -> Predicate
wlp Skip q = q
wlp (Assign t e) q = subst e t q
wlp (Block stmts) q = foldr wlp q stmts
wlp (Assert e) q = toPred e <^> q
wlp (Assume e) q = toPred e <=>> q
wlp (NDet s t) q = wlp s q <^> wlp t q

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
