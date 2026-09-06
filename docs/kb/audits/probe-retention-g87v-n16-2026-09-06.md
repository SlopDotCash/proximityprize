# G87V n=16 archive retention audit

Retain `scripts/probes/_out_466_g87v_census_rank_n16.txt`. Its full 45-row replay passes and equals the archive after newline normalization. The replay calls the producer's census, modular-rank and full-census-coverage routines for every nontrivial 16th root at primes 97,193,257. It reproduces the archive's single auxiliary-prime rank at 1000003; this is not the producer's larger default n=32 run.

Independent trial division verifies the field primes and both configured auxiliary primes. Elimination products are bounded by the square of the auxiliary modulus, below the signed int64 limit. At t=-1, each chosen six-coordinate support has exactly 20 sign assignments summing to zero after sign adjustment; C(16,6)*20=160160 independently reproduces each order-two census size.

Full modular rank certifies full rational rank. Deficient modular rank alone does not certify the exact rational rank, even when two primes agree. The reported coverage concerns the entire census. No newly compiled Lean fence theorem, all-scale forcing result, or production spectral bound is claimed. The corrected producer's threshold and interpretation supersede its historical prose.

The companion JSON records the source/archive hashes and complete output. Baseline reconciliation: this archive was not in the original 92 unreferenced artifacts. Its replay remains valid additional evidence, but the former increment to 60/92 was incorrect and must be removed from subsequent aggregate counts. The separate full archive is not covered. Three restored runtime helpers remain additional to the original inventory of 420 retained artifacts and one removed artifact.
