{-# LANGUAGE OverloadedStrings #-}
module TestPrograms where

import           Prelude hiding ((&&), (/=), (<), (<=), (==), (>), (>=), (||))

import           GCL.DSL

-- * Examples

allPrograms = [ simple, swap, minind ]

swap = program "swap" ["a" `as` array int, "i" `as` int, "j" `as` int] ["a'" `as` array int] $ do
  var ["tmp" `as` int, "a_old" `as` array int] $ do
    "a_old" $= "a"
    "tmp"     $= "a" ! "i"
    "a" ! "i" $= "a" ! "j"
    "a" ! "j" $= "tmp"
    "a'"      $= "a"
    assert $ "a'" ! "i" == "a_old" ! "j" && "a'" ! "j" == "a_old" ! "i"

minind = program "minind" ["a" `as` array int, "i" `as` int, "N" `as` int] ["r" `as` int] $ do
  var ["i0" `as` int] $ do
   "i0" $= "i"
   var ["min" `as` int] $ do
     ["min", "r"] $$= ["a" ! "i", "i"]
     let iv = "i" <= "N" && forall ("j" `as` int) ("i0" <= "j" && "j" < "i" ==> "a" ! "r" <= "a" ! "j")
     while iv ("i" < "N") $ do
       if_ ("a" ! "i" < "min")
         (["min", "r"] $$= ["a" ! "i", "i"])
         skip
       "i" $= "i" + 1
   assert $ forall ("j" `as` int) $ "i0" <= "j" && "j" < "N" ==> "a" ! "r" <= "a" ! "j"

simple = program "simple" [ "i" `as` int, "j" `as` int] ["r" `as` int ] $ do
  assume true
  "r" $= "i" + "j"
  -- ["r", "i"] $$= ["i", "r"]
  assert $ "r" == "i" && forall ("r" `as` int) ("r" == "r")
