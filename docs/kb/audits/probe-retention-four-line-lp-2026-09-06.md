# Four-line fractional LP retention review

Retain `scripts/probes/probe_rate_quarter_mu16_four_line_amplifier_lp.py` as an exact rational optimization probe. The full run with SymPy 1.14.0 completed all 29 candidates and exited successfully. A wrapper substituted each returned assignment into every constraint using exact arithmetic and checked equality of its objective with the reported value. The source now performs these checks itself. The companion JSON preserves the wrapper, output, and current source hash.

Two candidates report 77/9 for the minimum core per fibre unit, corresponding to agreement density 77/144 and radius 67/144. The other 27 report 49/6. These are solver-reported optima with checked primal assignments; this review does not supply independent dual certificates of optimality.

The candidate set is the intersection of four finite-prime censuses. This replay does not establish universality over all primes. The model permits fractional allocation and the non-strict common-factor budget sum g <= 1; realizing deg G < m requires a separate finite integer construction and rounding argument. Neither this LP nor its checked assignments complete the production Delta Star theorem.

Membership in the original 92-file unreferenced inventory was checked directly. This review advances the corrected aggregate from 72 to 73 reviewed, with 19 remaining. Retention preserves useful evidence rather than treating lack of direct filename references as grounds for deletion.
