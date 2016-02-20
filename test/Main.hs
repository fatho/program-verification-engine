module Main where

import           Control.Monad
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           TestPrograms

main :: IO ()
main = forM_ allPrograms $ \prog -> do
  PP.displayIO stdout $ PP.renderPretty 0.6 100 (either PP.pretty PP.pretty prog)
  putStrLn ""
