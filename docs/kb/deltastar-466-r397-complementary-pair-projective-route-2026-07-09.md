# R397: complementary-pair projective route (2026-07-09)

Status: two broad combinatorial hypotheses refuted; a sharper dyadic projective classification survives.

## Complementary-pair reduction (`k=4` only)

In the `k=4` overlap-three saturated rate-quarter cell, an off-line point has a root block of size
three inside a petal of size five.  Replace the block by its complementary unordered pair.
Modulo the cubic locator of the three common anchors, compatibility says that the two block
locators have proportional values at those anchors.

For a petal `L` and pair `{x,y}` this projective value is, up to a fixed petal factor, the
coefficient point of the monic quadratic

```text
(X-x)(X-y) = X^2-(x+y)X+xy.
```

Three distinct anchors determine a quadratic projectively, and monicity fixes the scalar.
Thus each side's complementary-pair map is injective.  Compatibility is the intersection of two
finite pair configurations in `P^2` under one projectivity.

## Refutation 1: adjacency alone is quadratic

Ignoring the locator values leaves a partial bijection between edges of two `K_v` graphs,
`v=k+1`, in which no two selected pairs are adjacent in both coordinates.  This does not have a
linear bound.  For `v=2m`, odd `m`, split each vertex set into two `m`-sets and select

```text
left(a,b)  = {(0,a),(1,b)},
right(a,b) = {(0,a+b),(1,a-b)}             over Z/mZ.
```

Both projections are injective.  Sharing either left endpoint forces both right endpoints to
differ, so the forbidden double adjacency never occurs.  The family has `m^2=v^2/4` elements,
already exceeding the desired `4(v-1)` at `m=9`, where `81>68`.

`scripts/probes/probe_rate_quarter_edge_matching_z3.py` verifies the construction and also gives
the exact small maxima `5,9,10` for `v=5,6,7`.

## Refutation 2: pair-point lines are not only stars

The coefficient points `[1,-(x+y),xy]` for dyadic-domain pairs have two large line types:

1. stars through a fixed endpoint, with `n-1` points;
2. constant-product fibers `xy=c`, with `n/2` points.

Exact censuses in `scripts/probes/probe_dyadic_pair_quadratic_collinearity.py` find maximum
non-star line sizes `4` for the order-eight subgroup of `F17` and `8` for the order-sixteen
subgroup of `F97`.  Witness pairs have exponent sums `i+j=c mod n`.

Therefore the claim that every three collinear pair points share an endpoint is false.  The
failure is nevertheless rigid: it is the multiplicative involution `x -> c/x`, the same pairing
geometry that appears in the dyadic square-map recursion.

## Scope correction

This pair model does **not** generalize verbatim.  For arbitrary `k`, two size-`2k` cores with
intersection three have petals of size `2k-3`; a saturated root block has size `k-1`, and its
complement has size `k-2`.  The general invariant is therefore a subset-product point in `P^2`,
not a quadratic coefficient point.  R397 explains the completed `k=4` geometry and refutes two
possible abstractions, but it is not by itself an induction step.

## Surviving target

A closing theorem must retain the diagonal projectivity in the three-anchor evaluation basis.
For general `k`, bound fibers of the map sending a `(k-1)`-subset `S` of a `(2k-3)`-petal to

```text
[prod_{x in S}(a_0-x), prod_{x in S}(a_1-x), prod_{x in S}(a_2-x)] in P^2.
```

The pair-line classification remains a useful base-case model, while the general target is a
three-anchor subset-product collision theorem on the dyadic domain.

No prize closure is claimed in this round.
