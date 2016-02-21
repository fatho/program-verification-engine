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

import           Control.Lens.Plated
import           Data.Data
import           Data.Data.Lens
import           Data.Monoid
import           Data.String
import           Data.Typeable
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- | The type of names.
type Name = String

-- | Available types in our verification engine.
data Type = BoolType | IntType | ArrayType Type
  deriving (Eq, Ord, Show, Read, Data, Typeable)

-- | An unqualified reference to a variable, meaning depends on scope.
data UVar = UVar Name
  deriving (Eq, Ord, Show, Data, Typeable)

-- | Fully qualified and unique reference to a variable.
data QVar = QVar [Name] Int Type
  deriving (Eq, Ord, Show, Data, Typeable)

instance IsString UVar where
  fromString = UVar

-- | Available relational operators.
data RelOp = OpLEQ -- ^ Less than or equal
           | OpEQ  -- ^ Equal
           | OpGEQ -- ^ Greater than or equal
           | OpLT  -- ^ Less than
           | OpGT  -- ^ Greater than
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Data, Typeable)

data IntOp = OpPlus
           | OpMinus
           | OpTimes
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Data, Typeable)

data BoolOp = OpImplies
            | OpAnd
            | OpOr
  deriving (Eq, Ord, Show, Read, Enum, Bounded, Data, Typeable)

data Program = Program Name [Decl QVar] [Decl QVar] Statement
  deriving (Eq, Ord, Show, Data, Typeable)

data Decl var = Decl var Type
  deriving (Eq, Ord, Show, Data, Typeable)

data Statement = Skip
               | Assert Expression
               | Assume Expression
               | Assign [(QVar, Expression)]
               | Block [Statement]
               | NDet Statement Statement
               | While Expression Expression Statement
               | Var [Decl QVar] Statement
  deriving (Eq, Ord, Show, Data, Typeable)

data Expression = IntLit Int
                | BoolLit Bool
                | Ref QVar
                | BoolOp BoolOp Expression Expression
                | IntOp IntOp Expression Expression
                | RelOp RelOp Expression Expression
                | Index Expression Expression
                | RepBy Expression Expression Expression
                | NegExp Expression
                | ForAll (Decl QVar) Expression
  deriving (Eq, Ord, Show, Data, Typeable)

instance Plated Expression where
  plate = uniplate

instance Plated Statement where
  plate = uniplate

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

instance HasPrecedence RelOp where
  precedence _ = 4

instance HasPrecedence IntOp where
  precedence OpPlus  = 6
  precedence OpMinus = 6
  precedence OpTimes = 7

instance HasPrecedence BoolOp where
  precedence OpImplies = 1
  precedence OpAnd = 3
  precedence OpOr = 2

instance BinaryOperator BoolOp where
  associativity _ = RightAssoc

instance BinaryOperator RelOp where
  associativity _ = NoAssoc

instance BinaryOperator IntOp where
  associativity _ = LeftAssoc

instance PP.Pretty RelOp where
  pretty OpLEQ = "<="
  pretty OpEQ = "=="
  pretty OpGEQ = ">="
  pretty OpLT = "<"
  pretty OpGT = ">"

instance PP.Pretty IntOp where
  pretty OpPlus  = "+"
  pretty OpMinus = "-"
  pretty OpTimes = "*"

instance PP.Pretty BoolOp where
  pretty OpImplies = "==>"
  pretty OpAnd = "&&"
  pretty OpOr = "||"

instance PP.Pretty Type where
  pretty IntType = pptype "int"
  pretty BoolType = pptype "bool"
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
  pretty (QVar names id ty) = PP.hcat (PP.punctuate PP.dot (prefix ++ [real])) <> "$" <> PP.pretty id where
    prefix = map PP.pretty $ init names
    real   = ppident $ PP.pretty $ last names

instance PP.Pretty var => PP.Pretty (Decl var) where
  pretty (Decl var ty) = PP.hsep [PP.pretty var, PP.colon, PP.pretty ty]

instance PP.Pretty Expression where
  pretty e = go e 0 where
    go expr reqPrec = case expr of
      IntLit i -> PP.pretty i
      BoolLit b -> ppkeyword $ if b then "true" else "false"
      Ref qv -> PP.pretty qv
      BoolOp op e1 e2 -> prettyBinOp op (go e1) (go e2) reqPrec
      IntOp op e1 e2 -> prettyBinOp op (go e1) (go e2) reqPrec
      RelOp op e1 e2 -> prettyBinOp op (go e1) (go e2) reqPrec
      Index arr idx -> PP.pretty arr <> PP.brackets (go idx 0)
      RepBy arr idx e -> PP.pretty arr <> PP.parens (go idx 0 PP.<+> ppkeyword "repby" PP.<+> go e 0)
      NegExp e -> withParens (9 < reqPrec) ("!" <> go e 9)
      ForAll decl e -> withParens (0 < reqPrec) $ ppkeyword  "forall" PP.<+> PP.pretty decl <> PP.colon PP.</> go e 0

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

  pretty (NDet s1 s2) = PP.lbrace PP.<+> (PP.align $ PP.pretty s1) PP.</> PP.rbrace
      PP.<+> "[]" PP.<+> PP.lbrace PP.<+> (PP.align $ PP.pretty s2) PP.</> PP.rbrace

  pretty (While inv cond body) =
      ppkeyword "inv" PP.<+> PP.pretty inv PP.</>
      ppkeyword "while" PP.<+> PP.align (PP.pretty cond PP.</> ppkeyword "do") PP.<+> PP.lbrace PP.<$$>
      PP.indent 2 (PP.pretty body) PP.<$$> PP.rbrace

  pretty (Var decls blk@(Block _)) =
      ppkeyword "var" PP.<+> PP.align (PP.cat (PP.punctuate PP.comma (map PP.pretty decls)))
            PP.<+> ppkeyword "in"
            PP.<$$> PP.indent 2 (PP.pretty blk)
            PP.<$$> ppkeyword "end"
  pretty (Var decls single) =
      PP.hang 2 (ppkeyword "var" PP.<+> PP.align (PP.cat (PP.punctuate PP.comma (map PP.pretty decls)))
            PP.<+> ppkeyword "in"
            PP.</> PP.pretty single)
      PP.</> ppkeyword "end"

instance PP.Pretty Program where
  pretty (Program name inargs outargs stmt) = ppident (PP.text name) <> PP.hang 2 (PP.lparen PP.<+> argList PP.<+> PP.rparen) PP.<+> body where
    argList = PP.fillSep (PP.punctuate PP.comma (map PP.pretty inargs))
        PP.<+> "|" PP.</> PP.fillSep (PP.punctuate PP.comma (map PP.pretty outargs))
    body = PP.lbrace PP.<$$> PP.indent 2 (PP.pretty stmt) PP.<$$> PP.rbrace
