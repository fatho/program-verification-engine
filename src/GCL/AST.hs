{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE StandaloneDeriving        #-}
{- | Contains the AST of the Guarded Common Language.
-}
module GCL.AST where

import           Data.Monoid
import           Data.String
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type Name = String

data Type = BoolType | IntType | ArrayType Type
  deriving (Eq, Ord, Show, Read)

data Qualification = Qualified | Unqualified

data Var (q :: Qualification) where
  UVar :: Name -> Var Unqualified
  QVar :: [Name] -> Int -> Type -> Var Qualified

deriving instance Eq (Var q)
deriving instance Ord (Var q)
deriving instance Show (Var q)

instance IsString (Var Unqualified) where
  fromString = UVar

type QualifiedVar = Var Qualified
type UnqualifiedVar = Var Unqualified

data RelOp = OpLEQ
           | OpEQ
           | OpGEQ
           | OpLT
           | OpGT
  deriving (Show)

data IntOp = OpPlus
           | OpMinus
           | OpTimes
  deriving (Show)

data BoolOp = OpImplies
            | OpAnd
            | OpOr
  deriving (Show)

data Program = Program Name [Decl Qualified] [Decl Qualified] Statement
  deriving (Show)

data Decl (q :: Qualification) = Decl (Var q) Type
  deriving (Show)

data Statement = Skip
               | Assert Expression
               | Assume Expression
               | Assign [(QualifiedVar, Expression)]
               | Block [Statement]
               | NDet Statement Statement
               | While Expression Expression Statement
               | Var [Decl Qualified] Statement
  deriving (Show)

data Expression = IntLit Int
                | BoolLit Bool
                | Ref QualifiedVar
                | BoolOp BoolOp Expression Expression
                | IntOp IntOp Expression Expression
                | RelOp RelOp Expression Expression
                | Index Expression Expression
                | RepBy Expression Expression Expression
                | NegExp Expression
                | ForAll (Decl Qualified) Expression
  deriving (Show)


-- * Pretty Printing

type Precedence = Int

data Assoc = LeftAssoc | NoAssoc | RightAssoc
  deriving (Eq, Ord, Enum, Bounded, Show, Read)

class HasPrecedence op where
  precedence :: op -> Precedence

class HasPrecedence op => BinaryOperator op where
  associativity :: op -> Assoc

prettyBinOp :: (BinaryOperator op, PP.Pretty op) => op -> (Int -> PP.Doc) -> (Int -> PP.Doc) -> Precedence -> PP.Doc
prettyBinOp op l r reqPrec = withParens (precOp < reqPrec) $ PP.sep [l lprec, PP.pretty op, r rprec] where
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

instance PP.Pretty (Var q) where
  pretty (UVar name) = ppident $ PP.text name
  pretty (QVar names id ty) = PP.hcat (PP.punctuate PP.dot (prefix ++ [real])) <> "$" <> PP.pretty id where
    prefix = map PP.pretty $ init names
    real   = ppident $ PP.pretty $ last names

instance PP.Pretty (Decl q) where
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
    lpretty = PP.cat (PP.punctuate PP.comma (map PP.pretty lvals))
    rpretty = PP.cat (PP.punctuate PP.comma (map PP.pretty rvals))

  pretty (Block stmts) = PP.sep (PP.punctuate PP.semi (map PP.pretty stmts))
  pretty (NDet s1 s2) = undefined
  pretty (While inv cond body) = undefined

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
  pretty (Program name inargs outargs stmt) = ppident (PP.text name) <> PP.align (PP.lparen PP.<+> argList PP.<+> PP.rparen) PP.<+> body where
    argList = PP.sep (PP.punctuate PP.comma (map PP.pretty inargs))
        PP.</> "|" PP.<+> PP.sep (PP.punctuate PP.comma (map PP.pretty outargs))
    body = PP.lbrace PP.<$$> PP.indent 2 (PP.pretty stmt) PP.<$$> PP.rbrace
