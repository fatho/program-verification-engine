{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-| Defines the prover interface used by the WLP transformer, based on a free monad.
    This allows the WLP transformer to be a pure computation building an expression tree.
-}
module WLP.Interface
  ( Predicate
  , WlpOp (..)
  , WLP
  , MonadProver (..)
  , OutputMode (..)
  , CounterExample
  ) where

import qualified GCL.AST             as AST

import           Control.Monad.Free
import           Control.Monad.State
import           Data.Data
import qualified Data.Map.Strict     as Map

-- | The type of predicates.
type Predicate = AST.Expression

-- | A counter-example for a proof
-- TODO: change back
--type CounterExample = Map.Map AST.QVar String
type CounterExample = Map.Map String String

-- | The functor describing the actions available to the WLP transformer.
data WlpOp a
  = Prove Predicate (Maybe CounterExample -> a)
    -- ^ tries to prove the predicate and returns whether it was valid or not
  | Trace String a
    -- ^ outputs a trace message
  deriving (Functor, Typeable)

-- | The free monad executing the
type WLP = Free WlpOp

-- | A type class defining the interface for the prover monad needed by the WLP transformer.
class Monad m => MonadProver m where
  -- | tries to prove the predicate and returns a counter example if it is not valid
  prove' :: Predicate -> m (Maybe CounterExample)
  -- | tries to prove the predicate and returns whether it was valid or not
  prove :: Predicate -> m Bool
  prove pr = prove' pr >>= \case
    Nothing -> return True
    Just _ -> return False
  -- | outputs a trace message
  trace :: String -> m ()

-- | the free monad interface provides the required prover functions
instance MonadProver WLP where
  prove' predic = liftF (Prove predic id)
  trace msg  = liftF (Trace msg ())

instance MonadProver m => MonadProver (StateT s m) where
  prove' = lift . prove'
  trace = lift . trace

-- | output mode for interpreters
data OutputMode
  = TraceMode
    -- ^ trace the inner workings of the prover
  | SilentMode
    -- ^ only return the final results
  deriving (Show, Read, Eq, Ord, Enum, Bounded, Typeable, Data)
