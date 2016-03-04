{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{- | Contains the AST of the Guarded Common Language.
-}
module GCL.AST where
import           Data.String

import           Control.Lens.Plated
import           Data.Data
import           Data.Data.Lens
import           Data.Monoid
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
  deriving (Eq, Ord, Show, Data, Typeable)

data Expression = IntLit Int
                | BoolLit Bool
                | Ref QVar
                | BinOp Operator Expression Expression
                | Index Expression Expression
                | RepBy Expression Expression Expression
                | NegExp Expression
                | ForAll (Decl QVar) Expression
                | IfThenElse Expression Expression Expression
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

containsVar :: QVar -> Expression -> Bool
containsVar v p = Ref v `elem` universe p

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
{-
instance PP.Pretty (Var q) where
  pretty (UVar name) = ppident $ PP.text name
  pretty (QVar names id ty) = PP.hcat (PP.punctuate PP.dot (prefix ++ [real])) <> "$" <> PP.pretty id where
    prefix = map PP.pretty $ init names
    real   = ppident $ PP.pretty $ last names
-}
instance PP.Pretty UVar where
  pretty (UVar name) = ppident $ PP.text name

instance PP.Pretty QVar where
  pretty (QVar names uid _) = PP.hcat (PP.punctuate "_" (prefix ++ [real])) <> "_" <> PP.pretty uid where
    prefix = map PP.pretty $ init names
    real   = ppident $ PP.pretty $ last names

instance PP.Pretty var => PP.Pretty (Decl var) where
  pretty (Decl var ty) = PP.hsep [PP.pretty var, PP.colon, PP.pretty ty]

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
      ForAll decl e -> withParens (0 < reqPrec) $ ppkeyword "forall" PP.<+> PP.pretty decl <> PP.colon PP.</> go e 0
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

instance PP.Pretty Program where
  pretty (Program name inargs outargs stmt) = ppident (PP.text name) <> PP.hang 2 (PP.lparen PP.<+> argList PP.<+> PP.rparen) PP.<+> body where
    argList = PP.fillSep (PP.punctuate PP.comma (map PP.pretty inargs))
        PP.<+> "|" PP.</> PP.fillSep (PP.punctuate PP.comma (map PP.pretty outargs))
    body = PP.lbrace PP.<$$> PP.indent 2 (PP.pretty stmt) PP.<$$> PP.rbrace
