# G262: sponsor rank-5/rank-6 Wick/DC crossover

Date: 2026-07-13
Issue: #466
Branch: `research/proximity-prize` only (#499)

## Result

Let

```text
n  = 2^30
P1 = n(2^128 + 192) + 1
P2 = n(2^129 + 13) + 1.
```

For the Wick value and the unavoidable characteristic-p DC mass

```text
Wick_r    = (2r-1)!! n^r,
DCfloor_r = n^(2r)/q,
```

G261 proves the exact ratio

```text
Wick_r / DCfloor_r = (2r-1)!! q / n^r.
```

The sponsor fields lie strictly between adjacent subgroup powers:

```text
n^5 < P1 < n^6,
n^5 < P2 < n^6.
```

Therefore the direction of the Wick/DC comparison flips between the two live ranks:

```text
                     rank 5                         rank 6
P1       Wick > 241920 * DCfloor       DCfloor > 400 * Wick
P2       Wick > 483840 * DCfloor       DCfloor > 200 * Wick.
```

All four inequalities are proved division-free over exact sponsor integers. The companion probe uses `Fraction`; its floating-point renderings are diagnostic only.

## Characteristic-p census consequence

G63 proves that the actual primitive/wraparound collision census satisfies

```text
DCfloor_r <= census_r
```

at every prime and depth. G262 composes this with the rank-six sponsor inequalities:

```text
P1: 400 * Wick_6 < census_6,
P2: 200 * Wick_6 < census_6.
```

So the characteristic-zero Wick value cannot be an upper ceiling for the sponsor rank-six census. It is hundreds of times below the mass forced by the principal Fourier frequency alone. This is the exact characteristic-p wraparound crossover, not a constant-factor defect.

## General reverse-regime lemma

G262 also proves the clean converse to G261's thin-regime comparison:

```text
(2r-1)!! q < n^r  ==>  Wick_r < DCfloor_r.
```

Any quantity containing the DC mass is then strictly super-Wick. This statement isolates the binding inequality without sponsor numerics.

## Asymptotics

Write `q = n^beta`. Then

```text
log_n(Wick/DC) = beta - r + log_n((2r-1)!!).
```

At fixed rank and large `n`, the sign is controlled by the crossing `r = beta`, with the double-factorial term only shifting the boundary by `o(1)` in base `n`. Here

```text
beta(P1) = 5.266666... + negligible,
beta(P2) = 5.300000... + negligible,
```

so rank five is on the `Wick >> DC` side and rank six is on the `DC >> Wick` side. This adjacent-rank reversal is structural at the sponsor exponent, not a probe accident.

## FS15-FS18 integration

This result consumes the full FS15-FS18 arc:

- FS15 gives the raw Wick per-frequency ladder only at depth-r good primes.
- FS16 gives the sharp resultant envelope `(2r)^(n/2)` for the bad-prime certificate, improving height but not selecting a fixed sponsor prime.
- FS17 unions the fixed-depth good sets, but the deepest-rung budget remains dominant and cannot reach logarithmic depth.
- FS18 completes the odd/even Wick census and the simultaneous min-ladder, still only on the FS17 good set.
- G64 proves the sponsor field is forced exceptional at depth six from the DC mass.

G262 pins the sponsor arithmetic behind G64: at rank six the raw Wick inequality cannot hold because `Wick_6 < DCfloor_6 <= census_6`. No resultant refinement can select the sponsor prime out of the exceptional set at that rank without contradicting Parseval. At rank five, by contrast, G261's thin-regime comparison is valid but merely shows a very loose Wick-over-DC calibration.

## Scope

This is a sponsor-facing scope correction and a precise no-go for treating Wick as one uniform `r=5,6` census ceiling. It is not a bound on the row-labelled covariance, does not prove the production rank-five or rank-six signed gates, and does not close the prize.

The sole live CORE face remains the direct, row-labelled sponsor-prime Jacobi/cyclotomic covariance at ranks five and six. Generic moment, orbit-count, primitive-weighting, and FS almost-all-prime routes remain closed.

## Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G262SponsorRankCrossover.lean`
- Probe: `scripts/probes/g262_sponsor_rank_crossover_probe.py`
- Inputs: G63, G64, G261, FS15-FS18, both certified prize-prime modules
