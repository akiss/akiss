See README.md for instructions on how to compile. Make sure you
have Maude (version 2.7) installed, and accessible in your $PATH.

Validation suite
----------------

Several examples are used as part of our "validation suite".
It includes basic tests, analyses of RFID protocols AD, KCL, LAK,
LD, MW, OTYT and YPL, as well as analyses of NSL-xor and the guessing 
attack protocols direct-auth, nonce and secret-public-key. Analyses 
involve unlinkability and authentication properties as stated in the
paper. Examples with 2 sessions are provided in the examples directory
but are not analyzed in the validation suite. The validation suite is 
ran as follows:

    cd src
    make validate

Results are stored in `test_<date>_val/<test>.api.test/{log,time}`
files. The test suite takes 3mn to complete on a single 2.6GHz core.
You can pass options to benefit from parallelism on `N` cores:

    make AKISSOPTS="-j <N>" validate


The protocols are described in the following references:

 * T. van Deursen and S. Radomirovic. Attacks on rfid
   protocols. IACR Cryptology ePrint Archive, 2008:310,
   2008.

 * Y. Chevalier, R. Kusters, M. Rusinowitch, and
   M. Turuani. An NP decision procedure for protocol
   insecurity with XOR. In 18th IEEE Symposium on
   Logic in Computer Science (LICS’03), pages 261–270,
   Ottawa (Canada), 2003. IEEE Comp. Soc. Press.
