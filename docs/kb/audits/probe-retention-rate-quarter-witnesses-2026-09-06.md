# Retention mapping: rate-quarter witnesses — 2026-09-06

Two full default runs passed:

- `scripts/probes/probe_rate_quarter_common_factor_trade.py` checks the d=1 construction at n=2^30: two holes, triple core size two, agreement threshold 559240535, and n+2 labels. It checks the explicit hole labels, modular identities and disjointness tests, count/degree arithmetic, and the saturated-fibre coset tests. The saturated threshold is 592794965 and radius numerator 480946859. It does not enumerate the billion-point domain, test every d, independently certify the imported modulus/generator, or supply the abstract fibre-cardinality proof.
- `scripts/probes/probe_rate_quarter_five_clique_rank_counterexample.py` returns a valid non-single-pencil certificate over F_10007 at n=32, k=8, threshold 18. The producer reports constraint rank 23 and kernel dimension 17. Its 5000 general-position samples find no example without collinear triples; that negative search is not an impossibility proof. The successful certificate has exactly the four collinear triples among vertices 1,2,3,4, and vertex 0 lies outside their common pencil.

An independent certificate check recomputed polynomial evaluations, agreement
sets, pair overlaps, row-interpolation ranks, and all ten collinearity tests,
using separate modular elimination. It trial-divided 10007 to establish the
small field's primality. Actual agreement sizes are 18,27,24,22,22; the
minimum pair overlap is eight. Both received-row augmented Vandermonde
ranks are nine on every agreement set, excluding degree-below-eight joint
explanations. This independently validates the returned witness, not the
producer's constraint-rank calculation or its negative random search.

The miniature domain is the 32 integers 1..32 in F_10007, not the production
smooth subgroup. Neither run proves the production bad-count statement.
The companion JSON records source/helper hashes, full returned certificates,
and independent-check results. No Lean recompilation is claimed.

Both sources belonged to the original unreferenced cohort. This advances
that cohort to 48 of 92 reviewed, leaving 44. All artifacts remain retained.
