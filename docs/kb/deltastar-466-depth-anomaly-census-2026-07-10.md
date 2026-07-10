# Issue #466/#505: per-depth anomaly census — odd-depth nonpositivity at small n (CORRECTED)

> **CORRECTION (same day, ~1 h after landing).** The "subgroup law" framing below is
> **refuted at n = 32**: the concurrent G106 kernel certificate
> (`_G106OddDepthSignArithmeticRefutation.lean`, `p = 21523361`, `r = s = 5`) exhibits a
> strictly POSITIVE depth-five anomaly for an order-32 subgroup, and the concurrent
> falsification sweep found `DCEnergyBound` itself FALSE at `(n, p, r) = (64, 16778497, 5)`.
> What survives of this census: (i) the sharp subgroup-vs-random contrast at `n ≤ 16`
> (0/14 vs 16/44 violations) — subgroups are far more sign-structured than generic sets,
> but the structure DEGRADES with n and is not production-uniform; (ii) the per-depth and
> global budget checks (points 3–5); (iii) the probe itself, which measures the exact
> G96/G101 objects and remains the reference implementation for depth censuses at n ≤ 16.
> Do NOT build an odd-nonpos producer on this census. The G105 consumer's hypothesis must be
> per-prime or density-based, not uniform.

Date: 2026-07-10. Probe: `scripts/probes/probe_466_depth_anomaly_census.py` (exact integer
arithmetic; multiset enumeration + exchangeability DP for population fibers; reproducible,
seed 466).

## What was measured

The exact G96/G101 objects at accessible scale: `depthFiber(G, r, s)` (equal-sum pairs at G83M
maximal-cancellation depth `s`), `allPairsDepthFiber` (population), and the signed
`actualDepthAnomaly_s = q·depthFiber_s − allPairsDepthFiber_s`, for multiplicative subgroups
`n ∈ {4, 8, 16}` (two primes each, `p ≡ 1 mod n`, `p > n²`), rungs `r = 2..6`, plus 3 random
`n`-subsets of `ZMod p` per cell as control (44 control rows).

## Findings

1. **Odd-depth nonpositivity is a subgroup law, not a generic fact.**
   `actualDepthAnomaly_s ≤ 0` for every odd `s` in **all 14 subgroup cells** (every odd depth,
   every rung, every prime) — while **16 of 44 random-control cells violate it** (odd-depth
   positive anomalies appear freely for generic sets). This is precisely the missing
   hypothesis of the G105 odd-depth cancellation consumer: empirically it is TRUE for the
   prize objects and FALSE generically, i.e. it genuinely encodes multiplicative structure
   (as a usable theorem target must).
2. **Small subgroups alternate perfectly** (`+−+−+−…` at n = 4, 8 for all r ≤ 6); at n = 16
   the deep even depths can also go negative (e.g. `+−+−−` at r = 4) — even-depth positivity
   is NOT a law; only the odd-depth half survives.
3. **Depth-0/1 signs match the proven ladder** (G102 floor, G104 zero-fiber) in every cell.
4. **Per-depth positive anomalies each fit inside the full `q·Wick` budget** in every subgroup
   cell (`perdepth_ok=True` throughout) — the localized G96 route is not empirically dead at
   accessible scale, though `max_pos` can exceed `total` (cross-depth cancellation is real,
   consistent with G100).
5. **No DC violations**: `Σ_s anomaly_s ≤ q·Wick` in every cell, subgroup and random.

## Reading for the campaign

The live analytic target on the G96/G101 face can be split:
(a) prove `actualDepthAnomaly_s ≤ 0` for odd `s` for multiplicative subgroups — a *structural
sign law* that the census says is where the subgroup-ness lives; and
(b) bound the even-depth anomaly sum by `q·Wick` — the even depths carry the whole DC mass.
Any proof of (a) must use multiplicative structure (the random control kills all purely
combinatorial approaches at strength ≥ generic), which is the correct difficulty signature for
a wall-adjacent lemma.

## Honest scope

Floating-point-free but small-scale evidence; not a proof, not a prize claim. Rungs r ≤ 6,
n ≤ 16. A deeper sweep (n = 32, r ≥ 7 via sum-class pruning) is the natural red-team.
