{-# LANGUAGE TemplateHaskell #-}


import qualified GCL.AST                      as GCL
import qualified GCL.DSL                      as GCL
import qualified WLP.Interface                as Prover
import qualified WLP.Prover.SBV               as SBV
import qualified WLP.Wlp                      as WLP


import qualified Data.SBV                     as SBV
import           Criterion.Main

import qualified TestPrograms                 as Progs


main :: IO ()
main = defaultMain [
  bgroup "sequential"
    [ bgroup "fixPoint" [
        bench "loop1" $ nfIO $ Progs.loop1 `seqVerifyWith` fixConfig
      , bench "loop2" $ nfIO $ Progs.loop2 `seqVerifyWith` fixConfig ]
    , bgroup "unroll" [
        bench "loop1" $ nfIO $ Progs.loop1 `seqVerifyWith` unrollConfig
      , bench "loop2" $ nfIO $ Progs.loop2 `seqVerifyWith` unrollConfig ]
    ]
  , bgroup "parallel"
    [ bgroup "fixPoint" [
        bench "loop1" $ nfIO $ Progs.loop1 `parVerifyWith` fixConfig
      , bench "loop2" $ nfIO $ Progs.loop2 `parVerifyWith` fixConfig ]
    , bgroup "unroll" [
        bench "loop1" $ nfIO $ Progs.loop1 `parVerifyWith` unrollConfig
      , bench "loop2" $ nfIO $ Progs.loop2 `parVerifyWith` unrollConfig ]
    ]
  ]

myConfig :: WLP.WlpConfig Prover.WLP
myConfig = WLP.defaultConfig `WLP.withProcedures` [Progs.incSpec, Progs.minindSpec, Progs.swapSpec]

fixConfig :: WLP.WlpConfig Prover.WLP
fixConfig = myConfig { WLP.invariantInference = WLP.fixpointInference (Just 30) }

unrollConfig :: WLP.WlpConfig Prover.WLP
unrollConfig = myConfig { WLP.invariantInference = WLP.unrollInference WLP.UnrollAssert 40}

seqVerifyWith :: Either GCL.GclError GCL.Program -> WLP.WlpConfig Prover.WLP -> IO WLP.WlpResult
seqVerifyWith (Left err) _ = error $ "could not parse program: " ++ err
seqVerifyWith (Right prog) cfg = do
  let wlp = WLP.wlpProgram cfg prog
  SBV.interpretSBV SBV.z3 Prover.SilentMode (const $ return ()) wlp

parVerifyWith :: Either GCL.GclError GCL.Program -> WLP.WlpConfig Prover.WLP -> IO WLP.WlpResult
parVerifyWith (Left err) _ = error $ "could not parse program: " ++ err
parVerifyWith (Right prog) cfg = do
  let wlp = WLP.wlpProgram cfg prog
  SBV.parInterpretSBV SBV.z3 wlp
