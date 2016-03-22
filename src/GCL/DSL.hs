{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{- | Contains an embedded domain specific language for generating a
program in the Guarded Common Language represented by "GCL.AST".
-}
module GCL.DSL
  (
    -- * DSL Monad
    Code
  , CodeGenEnv (..)
  , CodeGenState (..)
  , VarInfo
  , varType
  , varQualifiedName
  , CodeBlock
  , GclError
  , runCode
  , execCode
    -- * Code Generation Primitives
  , declare
  , emit
  , extractCode
  , extractStmt
  , lookupVar
  , mkQualifiedVar
  , nested
  , unique
    -- * Program DSL
  , program
  , programFromSpec
    -- * Type DSL
  , int
  , boolean
  , array
  , as
    -- * Expression DSL
  , ExprAST (..)
  , true
  , false
    -- * Boolean Operators
  , (!) , (/\) , (\/) , (∧) , (∨) , (==>) , (<=>)
    -- * Relational Operators
  , (.<=) , (.>=) , (.>) , (.<) , (.==) , (./=)
    -- * Statement DSL
  , assert
  , assume
  , if_
  , invWhile
  , ndet
  , skip
  , var
  , while
  , call
  , ($=)
  , ($$=)
  ) where

import qualified GCL.AST              as AST

import           Control.Lens.Getter
import           Control.Lens.Lens
import           Control.Lens.Setter
import           Control.Lens.TH
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.RWS
import           Data.Foldable
import           Data.Map.Strict      (Map)
import qualified Data.Map.Strict      as Map
import           Data.String

-- * Code Generation

-- | Scope information about a declared variable.
data VarInfo = VarInfo
  { _varType          :: AST.Type
  -- ^ The type of the variable as given in the declaration.
  , _varQualifiedName :: AST.QVar
  -- ^ The fully qualified name of the variable, unqiue in the program.
  }
makeLenses ''VarInfo

-- | Environment with information needed during code generation.
data CodeGenEnv = CodeGenEnv
  { _declarations    :: Map AST.UVar VarInfo
  , _qualifiedPrefix :: [AST.Name]
  }
makeLenses ''CodeGenEnv

data CodeGenState = CodeGenState
  { _nextUnique :: Int
  }
makeLenses ''CodeGenState

-- | Output of code generation.
type CodeBlock = [AST.Statement]

-- | Errors occuring during code generation.
type GclError = String

-- | The code generation monad.
newtype Code a = Code { runCode' :: RWST CodeGenEnv CodeBlock CodeGenState (Except GclError) a }
  deriving (Functor, Applicative, Monad, MonadReader CodeGenEnv, MonadWriter CodeBlock, MonadState CodeGenState, MonadError GclError)

runCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (a, CodeGenState, CodeBlock)
runCode code e s = runExcept (runRWST (runCode' code) e s)

evalCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (a, CodeBlock)
evalCode code e s = runExcept (evalRWST (runCode' code) e s)

execCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (CodeGenState, CodeBlock)
execCode code e s = runExcept (execRWST (runCode' code) e s)

-- * Primitives

-- | Emits a single statement.
emit :: AST.Statement -> Code ()
emit stmt = tell [stmt]

-- | @extractCode m@ returns the code generated by @m@ without adding it to the current output.
extractCode :: Code () -> Code CodeBlock
extractCode gen = snd <$> censor (const mempty) (listen gen)

-- | Wraps the result of 'extractCode' in a 'AST.Block' statement.
extractStmt :: Code () -> Code AST.Statement
extractStmt = fmap AST.Block . extractCode

-- | Declares a program.
program :: AST.Name -> [AST.Decl AST.UVar] -> [AST.Decl AST.UVar] -> Code () -> Either GclError AST.Program
program name inputVars outputVars code = fst <$> evalCode ast initEnv initState where
  ast = declare inputVars $ \qinput ->
      declare outputVars $ \qoutput ->
        AST.Program name qinput qoutput <$> extractStmt code

  initEnv = CodeGenEnv
    { _declarations    = Map.empty
    , _qualifiedPrefix = [name]
    }

  initState = CodeGenState { _nextUnique = 0  }


-- | Creates a program from a specification.
programFromSpec :: AST.Name -> [AST.Decl AST.UVar] -> [AST.Decl AST.UVar] -> Code AST.Expression -> Code AST.Expression -> Either GclError AST.Program
programFromSpec name inputVars outputVars precondition postcondition = program name inputVars outputVars $ do
  assert precondition
  assume postcondition


-- | Returns a unique number.
unique :: Code Int
unique = nextUnique <<+= 1

-- | Creates a new qualified name.
mkQualifiedVar :: AST.UVar -> AST.Type -> Code AST.QVar
mkQualifiedVar (AST.UVar name) ty = do
  uid <- unique
  pr <- view qualifiedPrefix
  return $ AST.QVar (pr ++ [name]) uid ty

-- | Increases the nesting level for qualified names.
nested :: [AST.Name] -> Code a -> Code a
nested prefix = local (qualifiedPrefix %~ (++ prefix))

-- | Declares new variables.
declare :: [AST.Decl AST.UVar] -> ([AST.Decl AST.QVar] -> Code a) -> Code a
declare udecls body = do
  let newDecl (AST.Decl uv ty) (scope, decls)
        | Map.member uv scope = throwError "duplicate declaration in var"
        | otherwise           = do
            qv <- mkQualifiedVar uv ty
            return $ (Map.insert uv (VarInfo ty qv) scope, AST.Decl qv ty : decls)
  (newScope, qdecls) <- foldrM newDecl (Map.empty, []) udecls
  local (declarations %~ Map.union newScope) (body qdecls)

-- * Type DSL

int :: AST.Type
int = AST.BasicType AST.IntType

boolean :: AST.Type
boolean = AST.BasicType AST.BoolType

array :: AST.Type -> AST.Type
array (AST.BasicType ty) = AST.ArrayType ty
array _ = error "array must consist of values of a primitive type"

-- * Declaration DSL

-- | Syntactic sugar for declarations.
-- Example: @"foo" `as` array int@
as :: AST.UVar -> AST.Type -> AST.Decl AST.UVar
as = AST.Decl

-- * Expression DSL

-- | Searches for the qualified name of an unqualified reference in the current scope.
lookupVar :: AST.UVar -> Code AST.QVar
lookupVar uv@(AST.UVar name) = views declarations (Map.lookup uv) >>= \case
  Nothing -> throwError $ "variable '" ++ name ++ "' not declared"
  Just vi -> return $ view varQualifiedName vi

class ExprAST ast where
  type ExpVar ast :: *
  litI   :: Integer -> ast
  litB   :: Bool -> ast
  ref    :: ExpVar ast -> ast
  operator :: AST.Operator -> ast -> ast -> ast
  -- | Creates an array-indexing expression.
  arrIndex :: ast -> ast -> ast
  -- | Creates an array replacement expression.
  repBy :: ast -> ast -> ast -> ast
  -- | Creates a boolean negation.
  neg :: ast -> ast
  -- | Creates a forall quantifier.
  forall :: AST.Decl (ExpVar ast) -> ast -> ast
  -- | Creates an exists quantifier.
  exists :: AST.Decl (ExpVar ast) -> ast -> ast
  -- | If-then-else expression (ternary operator).
  ite :: ast -> ast -> ast -> ast

-- | A boolean true literal.
true :: ExprAST ast => ast
true = litB True

-- | A boolean false literal.
false :: ExprAST ast => ast
false = litB False

instance ExprAST AST.Expression where
  type ExpVar AST.Expression = AST.QVar

  litI = AST.IntLit
  litB = AST.BoolLit
  ref = AST.Ref
  operator = AST.BinOp
  arrIndex = AST.Index
  repBy = AST.RepBy
  neg = AST.NegExp
  forall = AST.Quantify AST.ForAll
  exists = AST.Quantify AST.Exists
  ite = AST.IfThenElse

instance ExprAST (Code AST.Expression) where
  type ExpVar (Code AST.Expression) = AST.UVar

  litI = return . AST.IntLit
  litB = return . AST.BoolLit
  ref uv = AST.Ref <$> lookupVar uv
  operator bo = liftM2 (AST.BinOp bo)
  arrIndex = liftM2 AST.Index
  repBy arr idx expr = liftM3 AST.RepBy arr idx expr
  neg = liftM AST.NegExp
  forall udecl quantExp = declare [udecl] $ \[qdecl] -> liftM (AST.Quantify AST.ForAll qdecl) quantExp
  exists udecl quantExp = declare [udecl] $ \[qdecl] -> liftM (AST.Quantify AST.Exists qdecl) quantExp
  ite = liftM3 AST.IfThenElse

-- | The array index operator.
infixl 9 !
(!) :: ExprAST ast => ast -> ast -> ast
(!) = arrIndex

infixr 3 /\
(/\) :: ExprAST ast => ast -> ast -> ast
(/\) = operator AST.OpAnd

infixr 2 \/
(\/) :: ExprAST ast => ast -> ast -> ast
(\/) = operator AST.OpOr

infixr 3 ∧
(∧) :: ExprAST ast => ast -> ast -> ast
(∧) = (/\)

infixr 2 ∨
(∨) :: ExprAST ast => ast -> ast -> ast
(∨) = (\/)

infixr 1 ==>
(==>) :: ExprAST ast => ast -> ast -> ast
(==>) = operator AST.OpImplies

infixr 1 <=>
(<=>) :: ExprAST ast => ast -> ast -> ast
(<=>) = operator AST.OpIff

infix 4 .<=
(.<=) :: ExprAST ast => ast -> ast -> ast
(.<=) = operator AST.OpLEQ

infix 4 .>=
(.>=) :: ExprAST ast => ast -> ast -> ast
(.>=) = operator AST.OpGEQ

infix 4 .>
(.>) :: ExprAST ast => ast -> ast -> ast
(.>) = operator AST.OpGT

infix 4 .<
(.<) :: ExprAST ast => ast -> ast -> ast
(.<) = operator AST.OpLT

infix 4 .==
(.==) :: ExprAST ast => ast -> ast -> ast
(.==) = operator AST.OpEQ

infix 4 ./=
(./=) :: ExprAST ast => ast -> ast -> ast
(./=) x y = neg (x .== y)

-- | Allows the usage of strings directly as references in our AST.
instance IsString (Code AST.Expression) where
  fromString = ref . fromString

-- | Allows the usage of strings directly as QVars in our AST.
instance IsString (Code AST.QVar) where
  fromString = lookupVar . fromString

-- | Allows the usage of the DSL AST in arithmetic expressions.
instance Num (Code AST.Expression) where
  (+) = operator AST.OpPlus
  (-) = operator AST.OpMinus
  (*) = operator AST.OpTimes
  abs e = liftM abs e
  signum e = liftM signum e
  fromInteger = litI

-- * Statement DSL
{-
class StmtAST ast where
  type Expr ast :: *
  skip     :: ast
  assert   :: Expr ast -> ast
  assume   :: Expr ast -> ast
  ndet     :: ast -> ast -> ast
  while    :: Expr ast -> ast -> ast
  invWhile :: Expr ast -> Expr ast -> ast -> ast
  assign   :: -}

skip :: Code ()
skip = emit $ AST.Skip

assert :: Code AST.Expression -> Code ()
assert e = e >>= emit . AST.Assert

assume :: Code AST.Expression -> Code ()
assume e = e >>= emit . AST.Assume

ndet :: Code () -> Code () -> Code ()
ndet left right = do
  leftAst <- extractStmt left
  rightAst <- extractStmt right
  emit $ AST.NDet leftAst rightAst

while :: Code AST.Expression -> Code () -> Code ()
while loopGuard body = do
  cnd <- loopGuard
  bodyStmt <- extractStmt body
  emit $ AST.InvWhile Nothing cnd bodyStmt

invWhile :: Maybe (Code AST.Expression) -> Code AST.Expression -> Code () -> Code ()
invWhile invariant loopGuard body = do
  inv <- sequence invariant
  cnd <- loopGuard
  bodyStmt <- extractStmt body
  emit $ AST.InvWhile inv cnd bodyStmt

call :: AST.Name -> [Code AST.Expression] -> [Code AST.QVar] -> Code ()
call prog args rets = do
  ins <- sequence args
  outs <- sequence rets
  emit $ AST.Call prog ins outs

infix 0 $$=
($$=) :: [Code AST.Expression] -> [Code AST.Expression] -> Code ()
($$=) lvals rvals = transformAll lvals rvals >>= emit . AST.Assign where
  transformAll [] []           = return []
  transformAll (vm:vs) (em:es) = do
      v <- vm
      e <- em
      (:) <$> transformArrAssign v e <*> transformAll vs es
  transformAll _ _             = throwError "non-matching number of values in multi-assignment"

  transformArrAssign (AST.Ref v)     expr = return (v, expr)
  transformArrAssign (AST.Index a i) expr = transformArrAssign a (AST.RepBy a i expr)
  transformArrAssign _               _    = throwError "expression is not an lvalue"

infix 0 $=
($=) :: Code AST.Expression -> Code AST.Expression -> Code ()
($=) lval rval = [lval] $$= [rval]

var :: [AST.Decl AST.UVar] -> Code () -> Code ()
var udecls body = declare udecls $ \qdecls -> do
  bodyStmt <- extractStmt body
  emit $ AST.Var qdecls bodyStmt

if_ :: Code AST.Expression -> Code () -> Code () -> Code ()
if_ cond then_ else_ = ndet (assume cond >> then_) (assume (neg cond) >> else_)
