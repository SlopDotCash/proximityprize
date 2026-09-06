# Retention mapping: ANT46 dyadic recurrence — 2026-09-05

The full default run of `scripts/probes/probe_ant46_kappa_dyadic_recurrence.py`
completed with exit zero. Its adjacent JSON stores the output and source hash.
This maps one additional original unreferenced artifact: 25 of 92 mapped,
67 remaining. No research artifact is deleted.

The script reconstructs integer polynomials through K32 by Newton identities,
checks the dyadic factorization and resultant evaluations, and rejects its two
specified scalar recurrence candidates. Integer determinants use Bareiss
elimination with divisibility assertions. These are exact finite computations,
not a proof of the recurrence for all dyadic orders.

For orders 8, 16 and 32 it enumerates primes at most 500000 satisfying p=1 mod n.
Within this eligible set, discriminant/self-value divisibility agrees with an
independent finite-field signature collision check. The header now states the
eligibility restriction explicitly. The bad lists for orders 8 and 16 are
[17,41] and [17,97,113,193,257,337]; the full order-32 list is in the record.

The final section only checks arithmetic divisibility and bit lengths for two
large candidate moduli. It does not test their primality or compute the
production-order resultant. At n=2^30 the displayed polynomial has 2^29
coefficients and the final primitive factor has degree 2^28. The finite replay
therefore does not provide a production nonvanishing certificate, a logarithmic
algorithm, or a Lean proof. Its general determinant helper also assumes a
nonzero pivot can be found and is not a verified total routine for all matrices.
