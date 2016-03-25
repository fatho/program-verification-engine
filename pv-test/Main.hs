{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified WLP.Interface                as Prover
import qualified WLP.Prover.SBV               as SBV
import qualified WLP.Wlp                      as WLP

import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.IO.Class
import qualified Data.Map                     as Map
import qualified Data.SBV                     as SBV
import           System.IO
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           WLP.Examples.TestPrograms


prettyPrint :: (MonadIO m, PP.Pretty a) => Int -> a -> m ()
prettyPrint width = liftIO . PP.displayIO stdout . PP.renderSmart 0.6 width . (PP.<> PP.line) . PP.pretty

interpretTree :: PP.Pretty a => Prover.WLP a -> PP.Doc
interpretTree = iter run . fmap PP.pretty where
  run (Prover.Prove predi cont) =
    "?" PP.<+> PP.pretty predi
      PP.<$$> PP.indent 2 ("false:" PP.<+> PP.align (cont $ Just Map.empty))
      PP.<$$> PP.indent 2 ("true: " PP.<+> PP.align (cont Nothing))
  run (Prover.Trace msg cont) = "!" PP.<+> PP.string msg PP.<$$> cont

-- | A prover backend that asks for help via stdin/stdout.
interactiveProver :: Prover.WLP a -> IO a
interactiveProver = iterM run where
  run (Prover.Prove predi cont) = ask "valid?" predi >>= \case
    True -> cont Nothing
    False -> cont (Just Map.empty)
  run (Prover.Trace msg cont) = putStrLn msg >> cont
  ask q e = do
    putStr ": " >> liftIO (prettyPrint 100 e) >> putStrLn ""
    putStr (q ++ " [y/n]") >> hFlush stdout
    getLine >>= \case
      "n" -> return False
      "y" -> return True
      _   -> do
          putStrLn "invalid answer"
          ask q e

myConfig :: WLP.WlpConfig Prover.WLP
myConfig = WLP.defaultConfig `WLP.withProcedures` [incSpec, swap]

main :: IO ()
main = do
  forM_ allPrograms $ \case
   Left err -> putStrLn err
   Right prog -> do
     liftIO $ prettyPrint 100 prog
     putStrLn ""
     putStrLn ""

     let cfg = myConfig { WLP.invariantInference = WLP.fixpointInference Nothing }
         wlp = WLP.wlpProgram cfg prog
     result <- SBV.interpretSBV SBV.z3 Prover.TraceMode (prettyPrint 160) wlp
     --result <- SBV.parInterpretSBV SBV.z3 wlp
     {-
     let result = WLP.wlpProgram prog
     -}
     liftIO $ prettyPrint 100 $ result
     putStrLn ""
     --liftIO $ prettyPrint 100 $ interpretTree wlp
     putStrLn ""
