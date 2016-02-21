{-# LANGUAGE LambdaCase #-}
module Main where

import qualified GCL.AST                      as GCL
import qualified GCL.DSL                      as GCL
import qualified WLP.Wlp                      as WLP

import           Control.Monad
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           TestPrograms

prettyPrint :: PP.Pretty a => Int -> a -> IO ()
prettyPrint width = PP.displayIO stdout . PP.renderPretty 0.8 width . PP.pretty

main :: IO ()
main = forM_ allPrograms $ \case
  Left err -> putStrLn err
  Right prog@(GCL.Program _ _ _ s) -> do
    prettyPrint 100 prog
    putStrLn ""
    putStrLn ""
    prettyPrint 100 $ WLP.wlp s (GCL.BoolLit True)
    putStrLn ""
    putStrLn ""
