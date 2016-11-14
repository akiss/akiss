Akiss
=====

Akiss is a verification tool for checking trace equivalence of
security protocols. It works in the so-called symbolic model,
representing protocols by processes in the applied pi-calculus, and
allowing the user to describe various security primitives by an
equational theory. In order to show that two processes are trace
equivalent, Akiss derives a complete set of tests for each trace of
each process, using a saturation procedure that performs Horn clause
resolution with selection.

A detailed description of the underlying theory is available in the
following papers:

  * Rohit Chadha, Ștefan Ciobâcă, and Steve Kremer.
    [Automated verification of equivalence properties of cryptographic protocols](http://www.loria.fr/~skremer/Papers/CCK-esop12.pdf). In
    Programming Languages and Systems ---Proceedings of the 21th
    European Symposium on Programming (ESOP'12), pp. 108–127, Lecture
    Notes in Computer Science 7211, Springer, Tallinn, Estonia,
    March 2012.

  * Rohit Chadha, Vincent Cheval, Ștefan Ciobâcă, and Steve Kremer.
	[Automated verification of equivalence properties of cryptographic
	protocol.](https://hal.inria.fr/hal-01306561/document)
	ACM Transactions on Computational Logic, 2016. To appear.


The notion of everlasting indistinguishability is introduced in

  * Myrto Arapinis, Véronique Cortier, Steve Kremer, and Mark D. Ryan.
    [Practical Everlasting Privacy](http://www.loria.fr/~skremer/Papers/ACKR-post13.pdf). In
    Proceedings of the 2nd Conference on Principles of Security and
    Trust (POST'13), pp. 21–40, Lecture Notes in Computer Science
    7796, Springer, Rome, Italy, March 2013.


Build
-----

You will need OCaml; version 4.01 is known to work.

An experimental version of Akiss supporting the xor operator
also requires both Maude and Full Maude:

 * [maude](http://maude.cs.illinois.edu/w/index.php?title=The_Maude_System) (version 2.7)

You shouldn't need it if you don't use the feature. See XOR.md for more
information on that branch.

For parallelising the saturation process, Akiss needs the following library:

 * [nproc](https://github.com/MyLifeLabs/nproc)

This dependency is optional; when it is not available, Akiss will run
sequentially.

To build, just run `make`.


Statistics / tests
------------------

To run tests and collect statistics, run `make stats`. This will run
Akiss on a selection of examples from the `examples` directory. For
each `file.api` file processed, a `file.stats` file will be created
with statistics. The Makefile will pass the `AKISS_OPTIONS` variable
as arguments to the `akiss` executable, so you can for example run it
with 4 jobs with the following command:

    make stats AKISS_OPTIONS="-j 4"


Usage
-----

Usage:

    akiss [options] < specification-file.api

 * `--verbose`,`-verbose`: enable verbose output
 * `--debug`, `-debug`: enable debug output
 * `--output-dot <file>`: output statement graph to <file>
 * `-j <n>`: use `<n>` parallel jobs (if supported)
 * `--ac-compatible`: use the AC-compatible toolbox even on non-AC
   theories (experimental, needs maude and tamarin)
 * `--tamarin-variants`: use tamarin to compute variants in seed
   statements
 * `--check-generalizations`: check that generalizations of kept
   statements are never dropped
 * `--help`, `-help`: display this list of options

For example:

    akiss --verbose < examples/strong-secrecy/blanchet.api


A quick overview of specification files
---------------------------------------

Specification files consist of:

 * a preamble declaring used symbols and their arity, private names
   (public names are symbols of arity 0), channels and variables;
 * the definition of an equational theory;
 * process definitions;
 * queries.

### Preamble

The preamble is straightforward. Each item is a comma-separated list
of syntactic elements used in the file. Here is an example of
preamble:

    symbols pair/2, fst/1, snd/1, a/0, b/0;
    channels c;
    evchannels bb;
    privchannels p;
    var x, y, z;

There are three kinds of channels: regular, private and everlasting
channels. Regular channels represent channels used during a session of
a protocol. Private channels cannot be read by the adversary, and
always result in silent communication. Everlasting channels represent
channels whose transmitted data remains available when verifying
everlasting indistinguishability.

### Equational theory

The equational theory is a list of rewrite rules. Akiss will work
modulo this theory. For example:

    rewrite fst(pair(x, y)) -> x;
    rewrite snd(pair(x, y)) -> y;

Rewrite rules can be everlasting, i.e. they are used after the
interaction between the protocol and the adversary is finished when
verifying everlasting indistinguishability.

    evrewrite fst(pair(x, y)) -> x;
    evrewrite snd(pair(x, y)) -> y;

### Processes

The equational theory is followed by a list of process
declarations. They respect the following grammar:

    declaration ::= process_name = process;

    action ::=   in(channel, variable)
               | out(channel, term)
               | [term = term]

    process ::=   0 | process_name | action
                | action . process
                | let variable = term in process
                | process :: process
                | process || process
                | ( process )

The operator precedence is: `"in"` < `::` < `||` < `.`.

### Queries

Akiss can answer to a variety of queries, the main ones being:

 * `[not] equivalentct? P and Q;`: checks coarse-grain
   [in]equivalence of `P` and `Q`.
 * `[not] equavalentft? P and Q;`: checks fine-grain
   [in]equivalence of `P` and `Q`.
 * `[not] fwdequivalentft? P and Q;`: checks forward [in]equivalence
   of `P` and `Q`.
 * `print_traces P;`: The core of Akiss works on traces. After a
   process is parsed according to the high-level grammar given above,
   it is first expanded into a set of traces before running the core
   algorithm of Akiss.  For examples, `P1 || P2` results in all
   interleavings of `P1` and `P2`.  The `print_traces` query prints
   those traces.
 * `variants? t;`: prints the variants of term `t`.
 * `unifiers? t1 t2;`: prints equational unifiers of terms `t1` and `t2`.
 * `normalize? t;`: prints the normal form of term `t`.


Source tree
-----------

Here is a quick guide to the organization of the source code:

 * `util.ml`: misc utilities
 * `ast.ml`, `parser.mly`, `lexer.mll`: parsing of API files
 * `config.ml`: detects external tools
 * `term.ml`: term structure and basic operations on them
 * `lexmaude.mll`, `parsemaude.mly`, `maude.ml`: interface with maude
 * `lextam.mll`, `parsetam.mly`, `tamarin.ml`: interface with tamarin
 * `rewriting.ml`: unification and variants for non-AC theories
 * `theory.ml`: process first half of API file, setting up the theory and
   appropriate rewriting toolbox
 * `base.ml`: data structure for the saturation algorithm
 * `horn.ml`: the saturation procedure itself
 * `process.ml`: processes and various operations on them, including the
   creation of protocol-related seed statements
 * `seed.ml`: generation of seed statements
 * `lwt_compat_pure.ml`: compatibility layer for systems which lack nproc
 * `main.ml`: process second half of API file, create theory-related seed
   statements and and perform queries
