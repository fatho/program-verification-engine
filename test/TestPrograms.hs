{-# LANGUAGE OverloadedStrings #-}
module TestPrograms where

import           GCL.AST (Program)
import           GCL.DSL

-- * Examples

allPrograms :: [Either GclError Program]
allPrograms = [ d1, d2, swap, minind, simple, fixpointCheck ]

d1 :: Either GclError Program
d1 = program "D1" ["x" `as` int ] ["y" `as` int] $ do
  assume $ 0 .< "x"
  invWhile (Just $ 0 .<= "x") (0 .< "x") $ do
    "x" $= "x" - 1
  "y" $= "x"
  assert $ "y" .== 0

d2 :: Either GclError Program
d2 = program "D2" ["x" `as` int ] ["y" `as` int] $ do
  assume $ 2 .<= "x"
  invWhile (Just $ 0 .<= "x") (0 .< "x") $ do
    "x" $= "x" - 2
  "y" $= "x"
  assert $ "y" .== 0

swap :: Either GclError Program
swap = program "swap" ["a" `as` array int, "i" `as` int, "j" `as` int] ["a'" `as` array int] $ do
  var ["tmp" `as` int, "a_old" `as` array int] $ do
    "a_old" $= "a"
    "tmp"     $= "a" ! "i"
    "a" ! "i" $= "a" ! "j"
    "a" ! "j" $= "tmp"
    "a'"      $= "a"
    assert $ "a'" ! "i" .== "a_old" ! "j" /\ "a'" ! "j" .== "a_old" ! "i"

minind :: Either GclError Program
minind = program "minind" ["a" `as` array int, "i" `as` int, "N" `as` int] ["r" `as` int] $ do
  var ["i0" `as` int] $ do
   "i0" $= "i"
   var ["min" `as` int] $ do
     ["min", "r"] $$= ["a" ! "i", "i"]
     let iv = "i" .<= "N" /\ forall ("j" `as` int) ("i0" .<= "j" /\ "j" .< "i" ==> "a" ! "r" .<= "a" ! "j")
     invWhile (Just iv) ("i" .< "N") $ do
       if_ ("a" ! "i" .< "min")
         (["min", "r"] $$= ["a" ! "i", "i"])
         skip
       "i" $= "i" + 1
   assert $ forall ("j" `as` int) $ "i0" .<= "j" /\ "j" .< "N" ==> "a" ! "r" .<= "a" ! "j"

simple :: Either GclError Program
simple = program "simple" [ "i" `as` int, "j" `as` int] ["r" `as` int ] $ do
  assume $ "j" .== 0
  "r" $= "i" + "j"
  assert $ "r" .== "i"

fixpointCheck :: Either GclError Program
fixpointCheck = program "fixpointCheck" ["x" `as` int] ["y" `as` int ] $ do
  "y" $= "x"
  while ("y" .> 0) $ do
    "y" $= "y" - 1
  assert $ "y" .== 0
--
-- pCallCheck :: Either GclError Program
-- pCallCheck = program "pCallCheck" ["x" `as` int] ["r" `as` int] $ do
--   assume $ "x" .== 0
--   call "inc" "x" "r"
--   assert $ "r" .== 1
