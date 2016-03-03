{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
module WLP.Interface where

import qualified GCL.AST            as AST

import           Control.Monad.Free
import           Data.Data

type Predicate = AST.Expression

data WlpOp a
  = Prove Predicate (Bool -> a)
  | Trace String a
  deriving (Functor, Typeable)

type WLP = Free WlpOp

class Monad m => MonadProver m where
  prove :: Predicate -> m Bool
  trace :: String -> m ()

instance MonadProver WLP where
  prove predic = liftF (Prove predic id)
  trace msg  = liftF (Trace msg ())

data OutputMode
  = TraceMode
  | SilentMode
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Typeable, Data)
