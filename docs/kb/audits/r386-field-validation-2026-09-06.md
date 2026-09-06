# R386 prime-field input validation

The retained `probe_r386_unique_root_strata.py` accepted n=4, p=65 and exited successfully. The order condition alone did not reject this composite: 8 has order four modulo 65. This violates the probe's prime-field interpretation.

Input validation now checks the dyadic order, primality by exact trial division, and divisibility before allocating census data. Invalid inputs produce an argparse error. Two regression tests cover the composite counterexample and valid/invalid field-order pairs. The valid n=8, p=4129 replay exits zero: 96 keys, 416 sign-canonical differences, total relation mass 257024, no vanishing relation. These are finite results, not a general no-collision theorem.

Trial division can be slow for large user-supplied primes. No probabilistic acceptance or unsupported primality range is introduced. This input correction and small replay do not complete the artifact's broader retention review; coverage remains 57/92.
