Title:  Program Verification Engine
Author: Giovanni Garufi
        Fabian Thorand
Date:   March 25, 2016

# Build Instructions

## Building with Stack

The easiest way of building our project is to use the [stack](http://docs.haskellstack.org/en/stable/README/) tool.
It relies on the curated package sets provided by the FP Complete in their
stackage project, in theory guaranteeing reproducible build of Haskell applications.

`stack` will automatically install the required version of GHC (7.10.3) if not already present
and download the dependencies from a chosen conflict-free set (`lts-5.3`).

Building the application is then a matter of issueing `stack build`. 
The tests can be run with `stack test`.

## Building with Cabal

TODO
