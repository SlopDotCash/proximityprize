# G249 Cartesian row-selection barrier

Date: 2026-07-12
Branch: `research/proximity-prize`
Issue: #466

## Result

G248 audited the Lu--Zheng--Zheng Jacobi-distribution theorem against the quotient-Jacobi object in G228.  The obstruction is quantifier-level: the published theorem controls a two-dimensional Cartesian family of Jacobi phases, while the CORE covariance needs a fixed second-character row and then applies the rank-dependent weights `Rhat_r(χ)`.

G249 records the sharp finite barrier in Lean.  In an `m × m` Cartesian family, a single full row has exactly `m` points and therefore Cartesian density `1/m`, but that row is completely uncontrolled.  Thus any argument converting a global Cartesian discrepancy/error budget into uniform fixed-row control must beat the threshold `D < 1/m`.

The formal payload is `Frontier/_G249CartesianRowSelectionBarrier.lean`:

- `rowBad_card`: the one-row exceptional set has cardinality `m+1` in an `(m+1) × (m+1)` grid.
- `rowBad_contains_full_row` and `rowBad_zero_fiber_card`: the distinguished row is entirely exceptional.
- `rowBad_card_mul_eq_grid_card`: cardinal form of exact density `1/(m+1)`.

## Sponsor implication

At the sponsor parameters, G248 measured the strongest applicable published Cartesian discrepancy terms as:

```text
P1: best log2 D = -14.748, row threshold = -128, missing 113.252 bits
P2: best log2 D = -14.915, row threshold = -129, missing 114.085 bits
```

So ordinary Cartesian Jacobi equidistribution cannot select the weighted rows needed by the CORE covariance.  This is not a constant-optimization gap; it is a row-density quantifier gap.

## Scope

Route no-go only.  G249 does not estimate Jacobi sums, does not touch the signed sponsor-prime covariance, and does not close the proximity prize.  It prevents reusing unweighted Cartesian phase-cloud discrepancy as if it were a uniform row theorem.
