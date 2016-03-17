module Spec where

import qualified GCL.AST                      as GCL
import qualified GCL.DSL                      as GCL
import qualified WLP.Interface                as Prover
import qualified WLP.Prover.SBV               as SBV
import qualified WLP.Wlp                      as WLP

import           Control.Monad
import           Control.Monad.Free
import           Control.Monad.IO.Class
import qualified Data.SBV                     as SBV
import           System.IO
import           Test.Hspec
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified TestPrograms                 as Progs

prettyPrint :: (MonadIO m, PP.Pretty a) => Int -> a -> m ()
prettyPrint width = liftIO . PP.displayIO stdout . PP.renderSmart 0.6 width . (PP.<> PP.line) . PP.pretty

myConfig :: WLP.WlpConfig Prover.WLP
myConfig = WLP.defaultConfig `WLP.withProcedures` [Progs.incSpec, Progs.minindSpec, Progs.swapSpec]

shouldVerify :: Either GCL.GclError GCL.Program -> Expectation
shouldVerify pr = pr `shouldVerifyWith` myConfig

shouldVerifyWith :: Either GCL.GclError GCL.Program -> WLP.WlpConfig Prover.WLP -> Expectation
shouldVerifyWith (Left err) _ = expectationFailure $ "could not parse program: " ++ err
shouldVerifyWith (Right prog@(GCL.Program n _ _ _) ) cfg = do
  let wlp = WLP.wlpProgram cfg prog
  result <- SBV.interpretSBV SBV.z3 Prover.SilentMode (const $ return ()) wlp
  unless (WLP.wlpResultVerified result) $
    expectationFailure $ "failed to verify '" ++ n ++ "', counter-example" ++ show (WLP.wlpResultCounterExample result)

shouldNotVerify :: Either GCL.GclError GCL.Program -> Expectation
shouldNotVerify pr = pr `shouldNotVerifyWith` myConfig

shouldNotVerifyWith :: Either GCL.GclError GCL.Program -> WLP.WlpConfig Prover.WLP -> Expectation
shouldNotVerifyWith (Left err) _ = expectationFailure $ "could not parse program: " ++ err
shouldNotVerifyWith (Right prog@(GCL.Program n _ _ _) ) cfg = do
  let wlp = WLP.wlpProgram cfg prog
  result <- SBV.interpretSBV SBV.z3 Prover.SilentMode (const $ return ()) wlp
  when (WLP.wlpResultVerified result) $
    expectationFailure $ "unexpectedly able to verify '" ++ n ++ "'"

spec :: Spec
spec = do
  describe "base implementation" $ do
    it "can verify D1" $
      shouldVerify Progs.d1
    it "can verify minind (as in exercise)" $
      shouldVerify Progs.minindEx
    it "can verify minind (simplified)" $
      shouldVerify Progs.minind
    it "reject D2" $
      shouldNotVerify Progs.d2
  describe "array assignment" $ do
    it "can verify swap" $
      shouldVerify Progs.swap
  describe "program call" $
    it "can verify sort" $
      shouldVerify Progs.sort
  describe "loop reduction" $ do
    it "can verify loop1 with fixpoint" $
      Progs.loop1 `shouldVerifyWith` myConfig { WLP.invariantInference = WLP.fixpointInference (Just 3) }
    it "reject loop2 with fixpoint" $
      Progs.loop2 `shouldNotVerifyWith` myConfig { WLP.invariantInference = WLP.fixpointInference (Just 10) }
    it "reject loop1 with [while]^20" $
      Progs.loop1 `shouldNotVerifyWith` myConfig { WLP.invariantInference = WLP.unrollInference WLP.UnrollAssert 20 }
    it "reject loop2 with [while]^20" $
      Progs.loop2 `shouldNotVerifyWith` myConfig { WLP.invariantInference = WLP.unrollInference WLP.UnrollAssert 20 }
    it "can verify loop1 with <while>^4" $
      Progs.loop1 `shouldVerifyWith` myConfig { WLP.invariantInference = WLP.unrollInference WLP.UnrollAssume 4 }
    it "can verify loop2 with <while>^4" $
      Progs.loop2 `shouldVerifyWith` myConfig { WLP.invariantInference = WLP.unrollInference WLP.UnrollAssume 4 }

  describe "system test" $ do
    it "The Matrix is in order" $
      (1 :: Int) `shouldBe` 1
