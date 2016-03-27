#  Program Verification Engine

By Giovanni Garufi and Fabian Thorand

# Build Instructions

## Building with Stack

The easiest way of building our project is to use the [stack](http://docs.haskellstack.org/en/stable/README/) tool.
It relies on the curated package sets provided by the FP Complete in their
stackage project, in theory guaranteeing reproducible build of Haskell applications.

`stack` will automatically install the required version of GHC (7.10.3) if not already present
and download the dependencies from a chosen conflict-free set (`lts-5.3`).

Building the application is then a matter of issuing `stack build`.
The tests can be run with `stack test`.
Benchmarks can be run with `stack bench`

## Building with Cabal

If you choose to use cabal as a build system, the installation procedure is as
standard. Just navigate to the project root and type

    cabal sandbox init
    cabal install --only-dependencies --enable-benchmarks --enable-tests
    cabal build

Once the project is build you can will find the executables in the respective
folder.
Tests can be directly run with `cabal test` and similarly, benchmarks can be run
with `cabal bench`

# Running Examples

To run individual examples in trace mode (giving a more detailed view over the inner workings)
the `example-runner` executable can be used.
When using stack, it can be run with `stack exec example-runner` and when using cabal with
`cabal run example-runner`.