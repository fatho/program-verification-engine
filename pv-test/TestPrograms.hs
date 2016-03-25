{-# LANGUAGE OverloadedStrings #-}
module TestPrograms where

import           GCL.AST (Program)
import           GCL.DSL

-- * Examples

allPrograms :: [Either GclError Program]
allPrograms = [ d1, d2, swap, minind, minindEx, simple, fixpointCheck, callCheck, callCheck2, callSwap ]

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
  assume $ "i" .< "N"
  var ["i0" `as` int] $ do
   "i0" $= "i"
   var ["min" `as` int] $ do
     ["min", "r"] $$= ["a" ! "i", "i"]
     "i" $= "i" + 1 -- NB: this is different from the version of the exercise, therefore the invariant is simpler
     let iv = "i0" .< "N"  -- capture information about lower bound of range
           /\ "i0" .<= "i"
           /\ "i" .<= "N"  -- we never exceed the range
           /\ "i0" .<= "r"
           /\ "r" .< "i"
           /\ "min" .== "a" ! "r" -- r points to minimum element found so far
           /\ forall ("j" `as` int) ("i0" .<= "j" /\ "j" .< "i" ==> "a" ! "r" .<= "a" ! "j")
     invWhile (Just iv) ("i" .< "N") $ do
       if_ ("a" ! "i" .< "min")
         (["min", "r"] $$= ["a" ! "i", "i"])
         skip
       "i" $= "i" + 1
   assert $ forall ("k" `as` int) $ "i0" .<= "k" /\ "k" .< "N" ==> "a" ! "r" .<= "a" ! "k"


minindEx :: Either GclError Program
minindEx = program "minindEx" ["a" `as` array int, "i" `as` int, "N" `as` int] ["r" `as` int] $ do
  assume $ "i" .< "N"
  var ["i0" `as` int] $ do
   "i0" $= "i"
   var ["min" `as` int] $ do
     ["min", "r"] $$= ["a" ! "i", "i"]
     let iv = "i0" .< "N"  -- capture information about lower bound of range
           /\ "i0" .<= "i"
           /\ "i" .<= "N"  -- we never exceed the range
           /\ "i0" .<= "r"
           -- NB: here we need the more complicated invariant because in the beginning, r == i, whereas every time afterwards we have r < i
           /\ ("i" .== "i0" ==> "r" .== "i")
           /\ ("i" .> "i0" ==> "r" .< "i")
           /\ "min" .== "a" ! "r" -- r points to minimum element found so far
           /\ forall ("j" `as` int) ("i0" .<= "j" /\ "j" .< "i" ==> "a" ! "r" .<= "a" ! "j")
     invWhile (Just iv) ("i" .< "N") $ do
       if_ ("a" ! "i" .< "min")
         (["min", "r"] $$= ["a" ! "i", "i"])
         skip
       "i" $= "i" + 1
   assert $ forall ("k" `as` int) $ "i0" .<= "k" /\ "k" .< "N" ==> "a" ! "r" .<= "a" ! "k"

simple :: Either GclError Program
simple = program "simple" [ "i" `as` int, "j" `as` int] ["r" `as` int ] $ do
  assume $ "j" .== 0
  "r" $= "i" + "j"
  assert $ "r" .== "i"

fixpointCheck :: Either GclError Program
fixpointCheck = program "fixpointCheck" ["x" `as` int] ["y" `as` int ] $ do
  assume $ "x" .> 10
  "y" $= "x"
  while ("y" .> 0) $ do
    "y" $= "y" - 1
  assert $ "y" .== 0

callCheck2 :: Either GclError Program
callCheck2 = program "callCheck2" ["x" `as` int] ["r" `as` int] $ do
  var ["x0" `as` int] $ do
    "x0" $= "x"
    call "inc" ["x"] ["x"]
    call "inc" ["x"] ["x"]
    "r" $= "x"
    assert $ "r" .== ("x0" + 2)


callCheck :: Either GclError Program
callCheck = program "callCheck" ["x" `as` int] ["r" `as` int] $ do
  call "inc" ["x"] ["r"]
  call "inc" ["r"] ["r"]
  assert $ "r" .== ("x" + 2)

inc :: Either GclError Program
inc = program "inc" ["x" `as` int] ["r" `as` int] $ do
  "r" $= "x" + 1

incSpec :: Either GclError Program
incSpec = programFromSpec "inc" ["x" `as` int] ["y" `as` int] true ("y" .== "x" + 1)

callSwap :: Either GclError Program
callSwap = program "callSwap" ["a" `as` array int, "i" `as` int, "j" `as` int] ["r" `as` int] $ do
  var ["ai" `as` int, "aj" `as` int] $ do
    "ai" $= "a" ! "i"
    "aj" $= "a" ! "j"
    call "swap" ["a", "i", "j"] ["a"]
    assert ("a" ! "i" .== "aj" /\ "a" ! "j" .== "ai")
