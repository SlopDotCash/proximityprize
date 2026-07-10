# R399: common locator-line hypothesis (2026-07-09)

Status: faithful overlap-three invariant isolated; exact `n=32` evidence supports a sharp `2k`
bound, proof open.

## Simultaneous equations

For two size-`2k` reference cores meeting in three coordinates, let `L,R` be their disjoint
petals, each of size `2k-3`, and let `A={a0,a1,a2}` be the three coordinates outside their union.
An off-reference witness has `(k-1)`-root blocks `S subset L`, `T subset R` and residual forms

```text
q_gamma - line_L(gamma) = c_gamma P_S,
q_gamma - line_R(gamma) = d_gamma P_T.
```

The common-anchor factorization forces equality of projective locator points

```text
Phi(S) = [P_S(a0):P_S(a1):P_S(a2)] = Phi(T).
```

Agreement at the three uncovered coordinates forces `Phi(S)` onto one fixed projective line:
the vector `(P_S(a0),P_S(a1),P_S(a2))` lies in the span of the fixed base- and direction-error
vectors there.  Distinct scalars give distinct points on that line outside the degenerate joint
case.

Therefore the exact off-reference population is controlled by

```text
| line intersect Phi(C(L,k-1)) intersect Phi(C(R,k-1)) |.
```

## Exact evidence

`scripts/probes/probe_subset_locator_torus_fibers.py --identity` computes this object exactly for
each sampled configuration.  On the order-32 subgroup of `F97`, `k=8`, each petal contributes
`C(13,7)=1716` blocks and roughly 1,600 distinct projective points.

Across 2,000 random disjoint choices of anchors and petals, the successive maxima were

```text
11, 12, 13, 14, 15, 16,
```

and never exceeded

```text
16 = 2k.
```

The earlier guess `2k-3` is therefore refuted; `2k` is the current sharp hypothesis.  For
`n=16,k=4`, 1,000 trials reached only one common collinear point.

## Live conjecture

For a dyadic evaluation domain of length `4k`, disjoint three-anchor set `A` and petals `L,R`
of size `2k-3`, every projective line contains at most `2k` common locator points of
`Phi(C(L,k-1))` and `Phi(C(R,k-1))`.

A proof should use the two simultaneous squarefree factorizations, likely through a resultant or
exterior-power argument.  A bound for one locator image alone is false (line sections reach 35),
and an arbitrary diagonal-torus fiber is much worse (404).  The intersection and fixed parameter
are essential.

Even this conjecture closes only the off-reference population.  Full rate-quarter closure also
needs to charge points on the two reference lines within the remaining `2k` budget.

No prize closure is claimed in R399.
