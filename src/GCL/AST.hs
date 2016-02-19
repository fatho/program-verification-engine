{- | Contains the AST of the Guarded Common Language.
-}
module GCL.AST where

type Name = String
type Type = String
type Target = String
type Variable = (Name, Type)
data Operator = OpLEQ
              | OpEQ
              | OpGEQ
              | OpLT
              | OpGT
              | OpPlus
              | OpMinus
              | OpTimes
              | OpImplies
              | OpAnd
              | OpOr

data Program = Program Name Statement

data Statement = Skip
               | Assert Expression
               | Assume Expression
               | Assign (Target, Expression)
               | Block [Statement]
               | NDet Statement Statement
               | While Expression Expression Statement
               | Var [Variable] Statement

data Expression = IntLit Int
                | BoolLit Bool
                | Ref Name
                | BinaryOp Expression Operator Expression
                | NegExp Expression
                | ForAll Variable Expression
                -- missing name [ expression]
