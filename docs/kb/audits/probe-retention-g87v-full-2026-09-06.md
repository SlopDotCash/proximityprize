# G87V full census archive

Retain `scripts/probes/_out_466_g87v_census_rank_full.txt`. The full streamed producer exited 0, completing n=16 at primes 97,193,257 and n=32 at primes 641,769,1153. All six census/rank/coverage summary rows and six full-rank root counts match the archive. The corrected threshold and concluding interpretation intentionally differ.

Each cell enumerates every six-coordinate support and balanced three-plus/three-minus sign assignment, selecting the rows vanishing at each nontrivial root, and accumulates modular row bases and full-census coverage. The maximum n=32 census has C(32,6)*C(6,3)=18123840 rows at the order-two root. Independent arithmetic confirms that count; trial division verifies all six field primes and both auxiliary moduli. Small complete-matrix comparisons for the streaming implementation are recorded in `g87v-bounded-storage-2026-09-06.md` and its regression test.

Full rank modulo an auxiliary prime proves full rational rank. A deficient modular rank does not give a rational-rank upper bound. Coverage concerns all census rows, not a selected independent subfamily. The archived threshold had an extra factor of two in its denominator; the producer now reports (n/2)*log(6)/log(p). No general forcing theorem, production spectral bound, or new Lean compilation is established by this finite run.

Unlike the previously reviewed n=16-only archive, this full archive belongs to the original 92 unreferenced artifacts. The corrected aggregate advances from 70 to 71 reviewed, with 21 remaining. Issue #2 is not complete.
