# δ* #466 — normalized moment-ratio monotonicity probe (2026-07-08)

## Hypothesis

The prize moment route needs the DC-subtracted nonzero spectrum to be sub-Wick at logarithmic depth.
Define

```text
R_r(G) = Σ_{b≠0}|η_b|^(2r) / ((p-1)(2r-1)!! σ^(2r)),
σ² = mean_{b≠0}|η_b|².
```

Closing-grade hypothesis:

> For `G = μ_n` in the Burgess/prize regime, `R_r(G)` is nonincreasing in `r`.

If true, this would be a serious path to closure: a low-rung sub-Wick theorem would propagate to
all deeper moment rungs.  This is **not** the R20 log-convexity theorem; R20 says ordinary moment
ratios increase for any positive measure.  Here the Gaussian-normalized ratios may decrease because
the Wick denominator grows by `(2r+1)σ²`.

Probe: `scripts/probes/probe_r58_moment_ratio_monotonicity.py`.

## Result

Exact full-spectrum computations for dyadic subgroups:

| n | primes tested near `n^4` | monotonicity failures through r=10 |
|---:|---:|---:|
| 8 | 6 | 0 |
| 16 | 6 | 0 |
| 32 | 3 | 0 |

Representative rows:

```text
n=8  p=4129    R1=1.0000 R2=0.8730 R3=0.6619 R4=0.4357 R5=0.2502 R6=0.1265
n=16 p=65537   R1=1.0000 R2=0.9366 R3=0.8193 R4=0.6674 R5=0.5054 R6=0.3554
n=32 p=1048609 R1=1.0000 R2=0.9685 R3=0.9069 R4=0.8219 R5=0.7216 R6=0.6128
```

Random symmetric controls show the property is not formal:

```text
n=12 p=2017 random monotonicity failures=2/40, worst jump=0.0279
n=16 p=4129 random monotonicity failures=1/40, worst jump=0.0182
```

## Verdict

The monotone-normalized-ratio hypothesis **survives this probe** and is sharper than the generic
positive-measure facts.  It is not implied by symmetry alone, because random symmetric sets can
violate it.

This creates a clean possible theorem shape:

```text
R_{r+1}(μ_n) ≤ R_r(μ_n)  for all r in the prize range.
```

Together with any proved low-rung sub-Wick bound, this would propagate sub-Wickness to the deep
moment used by the prize.  The next proof attack should not try generic moment algebra; it must
use the multiplicative-subgroup/cyclotomic structure that makes the Wick-normalized ratios descend.
