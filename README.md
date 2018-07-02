Akiss
=====

This branch implements Akiss with dag


Build
-----

You will need OCaml; version 4.06 or above is required.


To build, just run `make` from the src directory.



Usage
-----

Usage:

    ./akiss [options] specification-file.api

* `--help`, `-help`: display the list of available options

For example:

    ./akiss -progress ../examples/dag/BAC-3sessions.api


A quick overview of specification files
---------------------------------------

The syntax of Akiss is similar to Deepsec: https://github.com/DeepSec-prover/deepsec
Look at the examples for more details.


Source tree
-----------

Here is a quick guide to the organization of the source code:

 * `util.ml`: misc utilities
 * `ast.ml`, `parser.mly`, `lexer.mll`: parsing of API files
 * `types.ml`: the declaration of the main types
 * `rewriting.ml`: unification and variants for non-AC theories
 * `process.ml`: processes and various operations on them
 * `base.ml`: data structure for the saturation algorithm
 * `horn.ml`: the saturation procedure itself
 * `bijection.ml`: data structure for the testing algorithm
 * `process_execution.ml`: functions to execute tests in the other process
 * `tests.ml`: functions to generate the tests of the second part of the algorithm
 * `theory.ml`: the main file
