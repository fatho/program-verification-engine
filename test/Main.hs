{-# LANGUAGE LambdaCase #-}
module Main where

import qualified GCL.AST                      as GCL
import qualified GCL.DSL                      as GCL
import qualified WLP.Prover.Interface         as Prover
import qualified WLP.Prover.SBV               as SBV
import qualified WLP.Wlp                      as WLP

import           Control.Monad
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           TestPrograms

prettyPrint :: PP.Pretty a => Int -> a -> IO ()
prettyPrint width = PP.displayIO stdout . PP.renderPretty 0.8 width . PP.pretty

-- | A prover backend that asks for help via stdin/stdout.
interactiveProver :: Prover.Backend IO
interactiveProver = Prover.Backend
    { Prover.satisfiable = ask "satisfiable?"
    , Prover.valid = ask "valid?"
    }
  where
    ask q e = do
      putStr ": " >> prettyPrint 100 e >> putStrLn ""
      putStr (q ++ " [y/n]") >> hFlush stdout
      getLine >>= \case
        "n" -> return False
        "y" -> return True
        _   -> do
            putStrLn "invalid answer"
            ask q e

main :: IO ()
main = do
  forM_ allPrograms $ \case
   Left err -> putStrLn err
   Right prog@(GCL.Program _ _ _ s) -> do
     prettyPrint 100 prog
     putStrLn ""
     putStrLn ""
     precond <- WLP.wlpProgramMonadic SBV.z3 prog
     {-
     let precond = WLP.wlpProgram prog
     -}
     prettyPrint 100 $ precond
     putStrLn ""
     Prover.valid SBV.z3 precond >>= print
     putStrLn ""
     putStrLn ""
