# R398: general locator torus fiber refuted (2026-07-09)

Status: exact finite-field counterexample to the three-anchor compatibility-only hypothesis.

## Hypothesis tested

For overlap-three size-`2k` reference cores in length `4k`, each off-line witness selects
`(k-1)` roots in each petal of size `2k-3`.  Reducing the two locator polynomials modulo the
cubic common-anchor locator gives a point in `P^2`.  Compatibility between left and right blocks
is equality after one diagonal projectivity in the three-anchor evaluation basis.

The proposed bound was that every diagonal-projectivity fiber contains at most `4k` pairs of
blocks.  This would have controlled the off-line population.

## Exact refutation

`scripts/probes/probe_subset_locator_torus_fibers.py` enumerates every block on each side and
hashes all pairs by their exact diagonal-projectivity ratio.

For the order-32 subgroup of `F97`, with `k=8`, disjoint three-anchor and two thirteen-petal
sets, a sampled configuration has a fiber of size

```text
404 > 32 = 4k.
```

The enumeration is exact for each sampled configuration: both sides have
`C(13,7)=1716` blocks, and all `1716^2` pairs are assigned to their projective ratio.  At the
`k=4,n=16` base case, analogous sampled maxima are only two, confirming that the completed
quadratic-complement argument is exceptional to low dimension.

## Consequence

Three-anchor locator compatibility alone cannot close the general overlap-three cell.  A real
witness carries additional equations omitted by this abstraction:

1. one common scalar `gamma`;
2. one leading locator coefficient on each reference residual;
3. agreement at all three coordinates outside the two-core union;
4. the received rows are fixed globally across every witness.

The next viable invariant is the simultaneous interpolation system on those three uncovered
coordinates, not the projective locator fiber by itself.  No prize closure is claimed here.
