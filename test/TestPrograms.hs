{-# LANGUAGE OverloadedStrings #-}
module TestPrograms where

import           Prelude hiding ((&&), (/=), (<), (<=), (==), (>), (>=), (||))

import           GCL.DSL

-- * Examples

allPrograms = [ swap, minind ]

swap = program "swap" ["a" `as` array int, "i" `as` int, "j" `as` int] ["a'" `as` array int] $ do
  var ["tmp" `as` int] $ do
    "tmp"     $= "a" ! "i"
    "a" ! "i" $= "a" ! "j"
    "a" ! "j" $= "tmp"
    "a'"      $= "a"

minind = program "minind" ["a" `as` array int, "i" `as` int, "N" `as` int] ["r" `as` int] $ do
  var ["min" `as` int] $ do
    ["min", "r"] $$= ["a" ! "i", "i"]
    while true ("i" < "N" - 1) $ do
      if_ ("a" ! "i" < "min")
        (["min", "r"] $$= ["a" ! "i", "i"])
        skip
      "i" $= "i" + 1

