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
{- | Contains an embedded domain specific language for generating a
program in the Guarded Common Language represented by "GCL.AST".
-}
module GCL.DSL where

import qualified GCL.AST              as AST

import           Control.Applicative
import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.RWS
import           Data.Foldable
import qualified Data.Map.Strict      as Map
import           Data.String


-- * Code Generation

-- | Scope information about a declared variable.
data VarInfo = VarInfo
  { _varType          :: AST.Type
  -- ^ The type of the variable as given in the declaration.
  , _varQualifiedName :: AST.QualifiedVar
  -- ^ The fully qualified name of the variable, unqiue in the program.
  }
makeLenses ''VarInfo

-- | Environment with information needed during code generation.
data CodeGenEnv = CodeGenEnv
  { _declarations    :: Map.Map AST.UnqualifiedVar VarInfo
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

newtype Code a = Code { runCode' :: RWST CodeGenEnv CodeBlock CodeGenState (Except GclError) a }
  deriving (Functor, Applicative, Monad, MonadReader CodeGenEnv, MonadWriter CodeBlock, MonadState CodeGenState, MonadError GclError)

runCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (a, CodeGenState, CodeBlock)
runCode code e s = runExcept (runRWST (runCode' code) e s)

evalCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (a, CodeBlock)
evalCode code e s = runExcept (evalRWST (runCode' code) e s)

execCode :: Code a -> CodeGenEnv -> CodeGenState -> Either GclError (CodeGenState, CodeBlock)
execCode code e s = runExcept (execRWST (runCode' code) e s)

emit :: AST.Statement -> Code ()
emit stmt = tell [stmt]

extractCode :: Code () -> Code CodeBlock
extractCode gen = snd <$> censor (const mempty) (listen gen)

extractStmt :: Code () -> Code AST.Statement
extractStmt = fmap AST.Block . extractCode

statementSeq :: [AST.Statement] -> AST.Statement
statementSeq = AST.Block

program :: AST.Name -> [AST.Decl AST.Unqualified] -> [AST.Decl AST.Unqualified] -> Code () -> Either GclError AST.Program
program name inputVars outputVars code = fst <$> evalCode ast initEnv initState where
  ast = declare inputVars $ \qinput ->
      declare outputVars $ \qoutput ->
        AST.Program name qinput qoutput <$> extractStmt code

  initEnv = CodeGenEnv
    { _declarations    = Map.empty
    , _qualifiedPrefix = [name]
    }

  initState = CodeGenState { _nextUnique = 0  }

unique :: Code Int
unique = nextUnique <<+= 1

mkQualifiedVar :: AST.UnqualifiedVar -> AST.Type -> Code AST.QualifiedVar
mkQualifiedVar (AST.UVar name) ty = do
  id <- unique
  pr <- view qualifiedPrefix
  return $ AST.QVar (pr ++ [name]) id ty

nested :: [AST.Name] -> Code a -> Code a
nested prefix = local (qualifiedPrefix %~ (++ prefix))

declare :: [AST.Decl AST.Unqualified] -> ([AST.Decl AST.Qualified] -> Code a) -> Code a
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
int = AST.IntType

boolean :: AST.Type
boolean = AST.BoolType

array :: AST.Type -> AST.Type
array = AST.ArrayType

-- * Declaration DSL

as :: AST.UnqualifiedVar -> AST.Type -> AST.Decl AST.Unqualified
as = AST.Decl

-- * Expression DSL

lookupVar :: AST.UnqualifiedVar -> Code AST.QualifiedVar
lookupVar uv@(AST.UVar name) = views declarations (Map.lookup uv) >>= \case
  Nothing -> throwError $ "variable '" ++ name ++ "' not declared"
  Just vi -> return $ view varQualifiedName vi

litI :: Int -> Code AST.Expression
litI = return . AST.IntLit

litB :: Bool -> Code AST.Expression
litB = return . AST.BoolLit

ref  :: AST.UnqualifiedVar -> Code AST.Expression
ref uv = AST.Ref <$> lookupVar uv

boolOp :: AST.BoolOp -> Code AST.Expression -> Code AST.Expression -> Code AST.Expression
boolOp bo = liftM2 (AST.BoolOp bo)

intOp  :: AST.IntOp -> Code AST.Expression -> Code AST.Expression -> Code AST.Expression
intOp io = liftM2 (AST.IntOp io)

relOp  :: AST.RelOp -> Code AST.Expression -> Code AST.Expression -> Code AST.Expression
relOp ro = liftM2 (AST.RelOp ro)

arrIndex :: Code AST.Expression -> Code AST.Expression -> Code AST.Expression
arrIndex = liftM2 AST.Index

repBy :: Code AST.Expression -> Code AST.Expression -> Code AST.Expression -> Code AST.Expression
repBy arr idx expr = liftM3 AST.RepBy arr idx expr

neg :: Code AST.Expression -> Code AST.Expression
neg = liftM AST.NegExp

forAll :: AST.Decl AST.Unqualified -> Code AST.Expression -> Code AST.Expression
forAll udecl quantExp = declare [udecl] $ \[qdecl] -> liftM (AST.ForAll qdecl) quantExp

infixl 9 !
(!) :: Code AST.Expression -> Code AST.Expression -> Code AST.Expression
(!) = arrIndex

instance IsString (Code AST.Expression) where
  fromString = ref . fromString

-- Statement DSL

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

while :: Code AST.Expression -> Code AST.Expression -> Code () -> Code ()
while invariant guard body = do
  inv <- invariant
  cnd <- guard
  bodyStmt <- extractStmt body
  emit $ AST.While inv cnd bodyStmt

infix 0 $$=
($$=) :: [Code AST.Expression] -> [Code AST.Expression] -> Code ()
($$=) lvals rvals = transformAll lvals rvals >>= emit . AST.Assign where
  transformAll [] []           = return []
  transformAll (vm:vs) (em:es) = do
      v <- vm
      e <- em
      (:) <$> transform v e <*> transformAll vs es
  transformAll _ _             = throwError "non-matching number of values in multi-assignment"

  transform (AST.Ref v)     expr = return (v, expr)
  transform (AST.Index a i) expr = transform a (AST.RepBy a i expr)
  transform _               _    = throwError "expression is not an lvalue"

infix 0 $=
($=) :: Code AST.Expression -> Code AST.Expression -> Code ()
($=) lval rval = [lval] $$= [rval]

var :: [AST.Decl AST.Unqualified] -> Code () -> Code ()
var udecls body = declare udecls $ \qdecls -> do
  bodyStmt <- extractStmt body
  emit $ AST.Var qdecls bodyStmt

if_ :: Code AST.Expression -> Code () -> Code () -> Code ()
if_ cond then_ else_ = ndet (assume cond >> then_) (assume (neg cond) >> else_)

-- * Examples

swap = program "swap" ["a" `as` array int, "i" `as` int, "j" `as` int] ["a'" `as` array int] $ do
  var ["tmp" `as` int] $ do
    "tmp"     $= "a" ! "i"
    "a" ! "i" $= "a" ! "j"
    "a" ! "j" $= "tmp"
    "a'"      $= "a"
