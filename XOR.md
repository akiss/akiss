See README.md for instructions on how to compile. Make sure you
have Maude **and** Full Maude (version 2.7) installed, and
accessible in your $PATH.

Validation suite
----------------

Several examples are used as part of our "validation suite".
It includes basic tests as well as simple tests on real
protocols, often simplified to single interleavings.
The validation suite is ran as follows:

    cd src
    make validate

Results are stored in `test_<date>_val/<test>.api.test/{log,time}`
files. The test suite takes 80mn to complete on a single 2.6GHz core.
You can pass options to benefit from parallelism on `N` cores:

    make AKISSOPTS="-j <N>" validate

Case studies
------------

A more thorough analysis of protocols is carried out in the
CCS test suite. It includes analyses of RFID protocols KCL, LAK, LD,
OTYT and YPL, as well as analyses of NSL-xor. Analyses involve
unlinkability and authentication properties. They involve several
interleavings and are thus computationally expensive; at the moment,
10+ hours are not unexpected, even when taking advantage of several
cores.

The protocols are described in the following references:

 * T. van Deursen and S. Radomirovic. Attacks on rfid
   protocols. IACR Cryptology ePrint Archive, 2008:310,
   2008.

 * Y. Chevalier, R. Kusters, M. Rusinowitch, and
   M. Turuani. An NP decision procedure for protocol
   insecurity with XOR. In 18th IEEE Symposium on
   Logic in Computer Science (LICS’03), pages 261–270,
   Ottawa (Canada), 2003. IEEE Comp. Soc. Press.
