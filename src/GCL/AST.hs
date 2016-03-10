{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{- | Contains the AST of the Guarded Common Language.
-}
module GCL.AST
  ( -- * AST types
    Name
  , PrimitiveType (..)
  , Type (..)
  , UVar (..)
  , QVar (..)
  , Operator (..)
  , Program (..)
  , Decl (..)
  , Statement (..)
  , Quantifier (..)
  , Expression (..)
    -- * AST Query Functions
  , containsVar
  , freeVariables
    -- * AST Manipulation
  , subst
  , quantifyFree
  , prenex
  , makeQuantifiersUnique
  )
  where
import           Data.String

import           Control.Lens
import           Control.Monad.State
import           Data.Data
import           Data.Data.Lens
import           Data.Map                     (Map)
import qualified Data.Map                     as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Set                     (Set)
import qualified Data.Set                     as Set
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- | The type of names.
type Name = String

-- | Available types in our verification engine.
data PrimitiveType = BoolType | IntType
  deriving (Eq, Ord, Show, Read, Data, Typeable)

-- | Available types in our verification engine.
data Type = BasicType PrimitiveType | ArrayType PrimitiveType
  deriving (Eq, Ord, Show, Read, Data, Typeable)

-- | An unqualified reference to a variable, meaning depends on scope.
data UVar = UVar Name
  deriving (Eq, Ord, Show, Data, Typeable)

-- | Fully qualified and unique reference to a variable.
data QVar = QVar [Name] Int Type
  deriving (Eq, Ord, Show, Data, Typeable)

data Operator = OpLEQ
              | OpEQ
              | OpGEQ
              | OpLT
              | OpGT
              | OpPlus
              | OpMinus
              | OpTimes
              | OpImplies
              | OpIff
              | OpAnd
              | OpOr
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Data, Typeable)

instance IsString UVar where
  fromString = UVar

data Program = Program Name [Decl QVar] [Decl QVar] Statement
  deriving (Eq, Ord, Show, Data, Typeable)

data Decl var = Decl var Type
  deriving (Eq, Ord, Show, Data, Typeable)

data Statement = Skip
               -- ^ the skip statement does nothing
               | Assert Expression
               -- ^ asserts that the given (boolean) expression holds, i.e. it adds another clause that needs to be proven
               | Assume Expression
               -- ^ assumes that the given (boolean) expression holds, i.e. it provides a known fact to the prover
               | Assign [(QVar, Expression)]
               -- ^ simultaneously assigns multiple variables to expressions
               | Block [Statement]
               -- ^ a sequential block of statements
               | NDet Statement Statement
               -- ^ a non-deterministic branch between to statements
               | InvWhile (Maybe Expression) Expression Statement
               -- ^ a while loop optionally annotated with an invariant
               | Var [Decl QVar] Statement
               -- ^ a declaration of variables
               | Call Name [Expression] [Expression]

  deriving (Eq, Ord, Show, Data, Typeable)

data Quantifier = ForAll | Exists
  deriving (Eq, Ord, Enum, Bounded, Read, Show, Typeable, Data)

data Expression = IntLit Int
                | Ref QVar
                | Index Expression Expression
                | RepBy Expression Expression Expression
                | NegExp Expression
                | IfThenElse Expression Expression Expression
                | BinOp Operator Expression Expression
                | BoolLit Bool
                | Quantify Quantifier (Decl QVar) Expression
  deriving (Eq, Ord, Show, Data, Typeable)

instance Plated Expression where
  plate = uniplate

instance Plated Statement where
  plate = uniplate

-- | Allows the usage of the AST in arithmetic expressions.
instance Num Expression where
  (+) = BinOp OpPlus
  (-) = BinOp OpMinus
  (*) = BinOp OpTimes
  abs e = IfThenElse (BinOp OpLT e 0) (negate e) e
  signum e = IfThenElse (BinOp OpLT e 0) (-1) (IfThenElse (BinOp OpEQ e 0) 0 1)
  fromInteger = IntLit . fromInteger

-- * Useful helper functions

containsVar :: QVar -> Expression -> Bool
containsVar v p = Ref v `elem` universe p

subst :: [(QVar, Expression)] -> Expression -> Expression
subst sub = transform $ \case
  v@(Ref name) -> fromMaybe v (lookup name sub)
  -- we don't need to worry about the binding of "foralls" at this
  -- point since the names have already been made unique
  other           -> other

freeVariables :: Expression -> Set QVar
freeVariables = para go where
  go (Ref qv) = Set.insert qv . Set.unions
  go (Quantify _ (Decl v _) _) = Set.delete v . Set.unions
  go _            = Set.unions

quantifyFree :: Quantifier -> Expression -> Expression
quantifyFree quantifier p = foldr quantify p (freeVariables p) where
  quantify qv@(QVar _ _ ty) inner = Quantify quantifier (Decl qv ty) inner

makeQuantifiersUnique :: Expression -> Expression
makeQuantifiersUnique expr = evalState (go (Map.fromSet id $ freeVariables expr) expr) (maxId + 1) where
  maxId = para maxId' expr

  maxId' (Ref (QVar _ uid _)) = max uid . maximum . (0 :)
  maxId' (Quantify _ (Decl (QVar _ uid _) _) _) = max uid . maximum . (0 :)
  maxId' _ = maximum . (0 :)

  go env (Ref var) = return $ Ref (env Map.! var)
  go env (Quantify q (Decl var@(QVar names _ _) ty) body) = do
    unique <- get
    put (unique + 1)
    let newVar = QVar names unique ty
    newBody <- go (Map.insert var newVar env) body
    return $ Quantify q (Decl newVar ty) newBody
  go env other = mapMOf plate (go env) other

-- | Converts a boolean expression into prenex normal form
prenex :: Expression -> Expression
prenex = transform pullQuantifiers . pushNeg False . elimArrows where
  elimArrows = transform $ \case
    BinOp OpImplies p q -> BinOp OpOr (NegExp p) q
    BinOp OpIff p q -> BinOp OpOr (BinOp OpAnd p q) (BinOp OpAnd (NegExp p) (NegExp q))
    x -> x

  pushNeg isNeg (BinOp OpAnd p q) = BinOp (if isNeg then OpOr else OpAnd) (pushNeg isNeg p) (pushNeg isNeg q)
  pushNeg isNeg (BinOp OpOr p q) = BinOp (if isNeg then OpAnd else OpOr) (pushNeg isNeg p) (pushNeg isNeg q)
  pushNeg isNeg (NegExp e) = pushNeg (not isNeg) e
  pushNeg isNeg (Quantify qua decl p) = Quantify (if isNeg then toggleQuant qua else qua) decl (pushNeg isNeg p)
  pushNeg True other = NegExp other
  pushNeg False other = other

  toggleQuant ForAll = Exists
  toggleQuant Exists = ForAll

  pullQuantifiers (BinOp OpAnd (Quantify qua decl p) q) = Quantify qua decl (pullQuantifiers $ BinOp OpAnd p q)
  pullQuantifiers (BinOp OpAnd p (Quantify qua decl q)) = Quantify qua decl (pullQuantifiers $ BinOp OpAnd p q)

  pullQuantifiers (BinOp OpOr (Quantify qua decl p) q) = Quantify qua decl (pullQuantifiers $ BinOp OpOr p q)
  pullQuantifiers (BinOp OpOr p (Quantify qua decl q)) = Quantify qua decl (pullQuantifiers $ BinOp OpOr p q)

  pullQuantifiers x = x

-- * Pretty Printing

type Precedence = Int

data Assoc = LeftAssoc | NoAssoc | RightAssoc
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

class HasPrecedence op where
  precedence :: op -> Precedence

class HasPrecedence op => BinaryOperator op where
  associativity :: op -> Assoc

prettyBinOp :: (BinaryOperator op, PP.Pretty op) => op -> (Int -> PP.Doc) -> (Int -> PP.Doc) -> Precedence -> PP.Doc
prettyBinOp op l r reqPrec = withParens (precOp < reqPrec) $ l lprec PP.<+> PP.pretty op PP.</> r rprec where
  precOp = precedence op
  assocOp = associativity op
  lprec  = if assocOp == LeftAssoc then precOp else precOp + 1
  rprec  = if assocOp == RightAssoc then precOp else precOp + 1

withParens :: Bool -> PP.Doc -> PP.Doc
withParens False = id
withParens True  = PP.parens

ppkeyword :: PP.Doc -> PP.Doc
ppkeyword = PP.blue

ppident :: PP.Doc -> PP.Doc
ppident = PP.red

pptype :: PP.Doc -> PP.Doc
pptype = PP.green

instance HasPrecedence Operator where
  precedence OpImplies = 1
  precedence OpOr = 2
  precedence OpAnd = 3
  precedence OpPlus  = 6
  precedence OpMinus = 6
  precedence OpTimes = 7
  precedence _ = 4

instance BinaryOperator Operator where
  associativity OpImplies = RightAssoc
  associativity OpAnd = RightAssoc
  associativity OpOr = RightAssoc
  associativity OpPlus  = LeftAssoc
  associativity OpMinus = LeftAssoc
  associativity OpTimes = LeftAssoc
  associativity _ = NoAssoc

instance PP.Pretty Operator where
  pretty OpLEQ = "<="
  pretty OpEQ = "=="
  pretty OpGEQ = ">="
  pretty OpLT = "<"
  pretty OpGT = ">"
  pretty OpPlus  = "+"
  pretty OpMinus = "-"
  pretty OpTimes = "*"
  pretty OpImplies = "==>"
  pretty OpIff = "<=>"
  pretty OpAnd = "&&"
  pretty OpOr = "||"

instance PP.Pretty PrimitiveType where
  pretty IntType = pptype "int"
  pretty BoolType = pptype "bool"

instance PP.Pretty Type where
  pretty (BasicType prim) = PP.pretty prim
  pretty (ArrayType ty) = pptype $ "[]" PP.<+> PP.pretty ty

instance PP.Pretty UVar where
  pretty (UVar name) = ppident $ PP.text name

instance PP.Pretty QVar where
  pretty (QVar names uid _) = PP.hcat (PP.punctuate "_" (prefix ++ [real])) <> "_" <> PP.pretty uid where
    prefix = map PP.pretty $ init names
    real   = ppident $ PP.pretty $ last names

instance PP.Pretty var => PP.Pretty (Decl var) where
  pretty (Decl var ty) = PP.hsep [PP.pretty var, PP.colon, PP.pretty ty]

instance PP.Pretty Quantifier where
  pretty ForAll = ppkeyword "forall"
  pretty Exists = ppkeyword "exists"

instance PP.Pretty Expression where
  pretty = flip go 0 where
    go expr reqPrec = case expr of
      IntLit i -> PP.pretty i
      BoolLit b -> ppkeyword $ if b then "true" else "false"
      Ref qv -> PP.pretty qv
      BinOp op e1 e2 -> prettyBinOp op (go e1) (go e2) reqPrec
      Index arr idx -> PP.pretty arr <> PP.brackets (go idx 0)
      RepBy arr idx e -> PP.pretty arr <> PP.parens (go idx 0 PP.<+> ppkeyword "repby" PP.<+> go e 0)
      NegExp e -> withParens (9 < reqPrec) ("!" <> go e 9)
      Quantify qua decl e -> withParens (0 < reqPrec) $ PP.pretty qua PP.<+> PP.pretty decl <> PP.colon PP.</> go e 0
      IfThenElse cond tval fval -> withParens (0 < reqPrec) (go cond 0 PP.<+> "->" PP.<+> go tval 0 PP.<+> "|" PP.<+> go fval 0)

instance PP.Pretty Statement where
  pretty Skip = ppkeyword "skip"
  pretty (Assert e) = ppkeyword "assert" PP.<+> PP.pretty e
  pretty (Assume e) = ppkeyword "assume" PP.<+> PP.pretty e
  pretty (Assign as) = PP.hang 2 (lpretty PP.<+> ":=" PP.</> rpretty) where
    (lvals, rvals) = unzip as
    lpretty = PP.fillSep (PP.punctuate PP.comma (map PP.pretty lvals))
    rpretty = PP.fillSep (PP.punctuate PP.comma (map PP.pretty rvals))

  pretty (Block stmts) = PP.sep (PP.punctuate PP.semi (map PP.pretty stmts))

  -- restore if expression
  pretty (NDet (Block (Assume g:s1)) (Block (Assume ng:s2)))
    | NegExp g == ng = ppkeyword "if" PP.<+> PP.align (PP.pretty g) PP.<+> ppkeyword "then" PP.<+> PP.lbrace
        PP.<$$> PP.indent 2 (PP.pretty (Block s1))
        PP.<$$> PP.rbrace PP.<+> ppkeyword "else" PP.<+> PP.lbrace
        PP.<$$> PP.indent 2 (PP.pretty (Block s2))
        PP.<$$> PP.rbrace

  pretty (NDet s1 s2) = PP.lbrace PP.<+> PP.align (PP.pretty s1) PP.</> PP.rbrace
      PP.<+> "[]" PP.<+> PP.lbrace PP.<+> PP.align (PP.pretty s2) PP.</> PP.rbrace

  pretty (InvWhile inv cond body) =
      ppkeyword "inv" PP.<+> PP.pretty inv PP.</>
      ppkeyword "while" PP.<+> PP.align (PP.pretty cond PP.</> ppkeyword "do") PP.<+> PP.lbrace PP.<$$>
      PP.indent 2 (PP.pretty body) PP.<$$> PP.rbrace

  pretty (Var decls blk@(Block _)) =
      ppkeyword "var" PP.<+> PP.align (PP.sep (PP.punctuate PP.comma (map PP.pretty decls)))
            PP.<+> ppkeyword "in"
            PP.<$$> PP.indent 2 (PP.pretty blk)
            PP.<$$> ppkeyword "end"
  pretty (Var decls single) =
      PP.hang 2 (ppkeyword "var" PP.<+> PP.align (PP.sep (PP.punctuate PP.comma (map PP.pretty decls)))
            PP.<+> ppkeyword "in"
            PP.</> PP.pretty single)
      PP.</> ppkeyword "end"
  pretty (Call name args rets) =
      ppkeyword "call" PP.<+> ppident (fromString name) PP.<+> PP.pretty args PP.<+> PP.pretty rets

instance PP.Pretty Program where
  pretty (Program name inargs outargs stmt) = ppident (PP.text name) <> PP.hang 2 (PP.lparen PP.<+> argList PP.<+> PP.rparen) PP.<+> body where
    argList = PP.fillSep (PP.punctuate PP.comma (map PP.pretty inargs))
        PP.<+> "|" PP.</> PP.fillSep (PP.punctuate PP.comma (map PP.pretty outargs))
    body = PP.lbrace PP.<$$> PP.indent 2 (PP.pretty stmt) PP.<$$> PP.rbrace
