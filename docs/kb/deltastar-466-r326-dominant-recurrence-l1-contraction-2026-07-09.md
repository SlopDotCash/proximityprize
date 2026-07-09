# Issue #466 R326: dominant-recurrence L1 contraction

Date: 2026-07-09

## Result

`_R326DominantRecurrenceL1Contraction.lean` replaces the ambient box estimate for a dominant
recurrence by the dimension-free inequality

```text
(|a|-b) * ||g||_1 <= ||v||_1,
```

assuming `v-a*g` has total `L1` mass at most `b*||g||_1`.  The file proves the concrete
permutation/binomial specialization where the residual is `c_i*g(sigma i)` and
`|c_i| <= b`.

For recurrence gap at least two, R324's endpoint identity

```text
||d||_1 = 2(r-s)
```

then gives

```text
s + ||g||_1 <= r
m^s * m^(||g||_1) <= m^r.
```

All four exported results are axiom-clean.

## Significance

R325's coordinate-box count has shape `K^m`, which is unusable when `m` is near `2^29`.
The `L1` contraction instead pairs a generator-count cost of order `m^k` with R322's
endpoint weight `m^(r-k)`.  Their ambient-dimension exponents cancel exactly at `m^r`.

This does not yet prove the full weighted census: one must count low-`L1` generators with
their factorial weights and discharge the dyadic saturation quotient.  It identifies a
route by which the dominant-binomial recurrence class can reach Wick scale without an
exponential-in-`m` loss.
