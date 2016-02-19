{-# LANGUAGE OverloadedStrings, GADTs, DataKinds, KindSignatures, ExistentialQuantification, FlexibleInstances #-}
{- | Contains the AST of the Guarded Common Language.
-}
module GCL.AST where
    
import Data.String

type Name = String
type Variable = Name

data Type = BoolType | IntType | ArrayType Type

data RelOp = OpLEQ
           | OpEQ
           | OpGEQ
           | OpLT
           | OpGT

data IntOp = OpPlus
           | OpMinus
           | OpTimes

data BoolOp = OpImplies
            | OpAnd
            | OpOr

data Program = Program Name [Decl] [Decl] Statement

data Decl = Decl Variable Type

data Statement = Skip
               | Assert Expression
               | Assume Expression
               | Assign [(Variable, Expression)]
               | Block [Statement]
               | NDet Statement Statement
               | While Expression Expression Statement
               | Var [Decl] Statement

data Expression = IntLit Int
                | BoolLit Bool
                | Ref Name
                | BoolOp BoolOp Expression Expression
                | IntOp IntOp Expression Expression
                | RelOp RelOp Expression Expression
                | Index Expression Expression
                | RepBy Expression Expression Expression
                | NegExp Expression
                | ForAll Variable Expression

{-
data Valueness = LValue | RValue

data Type = TInt | TBool | TArray Type

data Expression (v :: Valueness) (t :: Type) where
  IntLit  :: Int -> Expression 'RValue 'TInt
  BoolLit :: Bool -> Expression 'RValue 'TBool
  Ref     :: Name -> Expression 'LValue t
  RelOp   :: Expression v1 'TInt 
          -> RelOp 
          -> Expression v2 'TInt
          -> Expression 'RValue 'TBool
  BoolOp  :: Expression v1 'TBool
          -> RelOp
          -> Expression v2 'TBool
          -> Expression 'RValue 'TBool
  IntOp   :: Expression v1 'TInt 
          -> RelOp
          -> Expression v2 'TInt
          -> Expression 'RValue 'TInt
  Index   :: Expression v1 ('TArray el) 
          -> Expression v2 'TInt
          -> Expression 'RValue el
  RepBy   :: Expression v1 ('TArray el)
          -> Expression v2 'TInt
          -> Expression v3 el
          -> Expression 'RValue ('TArray el)
  BoolNeg :: Expression v 'TBool -> Expression 'RValue 'TBool
  ForAll  :: Variable -> Expression v 'TBool -> Expression 'RValue 'TBool
-}

instance Num Expression where
  (+) = IntOp OpPlus
  (-) = IntOp OpMinus
  (*) = IntOp OpTimes
  fromInteger = IntLit . fromInteger

instance IsString Expression where
  fromString = Ref
