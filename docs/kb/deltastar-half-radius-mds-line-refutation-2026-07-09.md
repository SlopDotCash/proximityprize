# Half-radius MDS line bound: refutation and surviving scope (2026-07-09)

## Verdict

The field-uniform projective incidence conjecture from the R382 audit is false:

> If `H` is an `[n,k]` MDS parity frame, `2e<n`, and `e+k+1<=n`, every projective
> syndrome line not contained in one `e`-support span has at most `n` points in
> `B_e = union_{|T|<=e} span(H_T)`.

The failure occurs for Reed--Solomon/Vandermonde frames and can exceed `n` in a fixed affine
chart.  It is therefore not caused by the projective infinity slot or by a non-GRS MDS arc.

## Machine-checked dyadic countermodel

`Frontier/_R383HalfRadiusMDSLineRefuted.lean` uses the eight roots of `X^8-1` in `F_17`
and the four-row Vandermonde columns

```text
v(x) = (1,x,x^2,x^3).
```

For the affine syndrome line `L(gamma)=(1,gamma,0,0)`, the file gives explicit
three-column decompositions for nine distinct parameters `gamma=1,...,9`.  For each support,
`L(0)` is proved outside the same span by pairing the four moment equations with
`(X-x)(X-y)(X-z)`.  Hence every displayed witness is proper.  The theorem
`exists_more_than_eight_proper_points` certifies `9>8=n`, while
`conjecture_hypotheses_hold` certifies

```text
2e = 6 < 8 = n,       e+k+1 = 3+4+1 = 8.
```

The companion exhaustive probe
`scripts/probes/probe_r383_half_radius_n8k4_exhaustive.py` enumerates all 89,030
projective lines in the syndrome space.  The failure is not isolated: its exact
proper-point histogram is

```text
8: 1,  12: 12,  13: 8,  14: 52,  15: 240,
16: 1,985,  17: 16,672,  18: 70,060.
```

Thus 70,060 lines have all `q+1=18` projective points proper.  The formal Lean
countermodel deliberately certifies only the nine points needed to refute the
proposed ceiling; the exhaustive census records how far the unrestricted claim fails.

This example already uses a two-power evaluation subgroup.  Its rate is `1/2`, so it refutes
the unrestricted MDS/GRS statement but not the production restriction `k<=n/4`.

## Strict-slack, low-rate countermodel

`Frontier/_HalfRadiusStrictSlackLowRateRefuted.lean` gives a second machine-checked
countermodel in the seven-dimensional syndrome space of a `[9,2]` RS code over `F_11`.
For the evaluation domain `0,...,8`, take the projective line spanned by

```text
a = (1,4,0,2,8,10,6),       b = (1,8,6,5,7,7,7).
```

Nine affine representatives `a+gamma*b`, for
`gamma in {0,1,3,4,5,6,7,9,10}`, and the point at infinity `b` have explicit
four-column decompositions.  The file proves that all ten representatives are nonzero and
pairwise projectively inequivalent, every displayed incidence is support-locally proper, and
no span of four distinct parity columns contains the fixed line.  It also proves the full
seven-row Vandermonde MDS property.  Thus there are ten proper projective points, while

```text
2e = 8 < 9 = n,       e+k+1 = 4+2+1 = 7 < 9,
4k = 8 <= 9.
```

This refutes both proposed repairs when used separately: strict slack in `e+k+1<n` does not
restore the ceiling, and neither does the low-rate condition `k<=n/4`.  The construction has
odd length and an interval evaluation domain, so it does not decide the even two-power
production specialization.

## Small plane model

There is also a transparent `[5,2]` example over `F_7`.  Take columns
`h_x=(1,x,x^2)` for `x=0,1,2,3,4` and the line `P:X+Z=0`.  All eight points of
`P(F_7)` lie on support secants; seven remain in the standard affine chart.  One support for
each finite slope, followed by the point at infinity, is

```text
t       0     1     2     3     4     5     6     infinity
{x,y} {2,4} {2,3} {0,3} {0,2} {1,3} {0,4} {0,1}   {3,4}
```

The secant through `h_x,h_y` has equation

```text
xy X - (x+y)Y + Z = 0.
```

On `P`, this becomes `(xy-1)X=(x+y)Y`, which verifies the table.  No chosen column
lies on `P`, since `1+x^2` is nonzero for `x=0,...,4` in `F_7`; therefore no support
secant equals `P`.  Thus the affine count is `7>5=n`.

## Infinite conic family

Ng and Wild define an `N`-arc covering a disjoint line when every point of that line lies on a
secant of the arc.  Their Theorem 4.5 constructs, for every `s | (q+1)` with `s>=3`, a subset
of a conic of size

```text
N = s + (q+1)/s - 1
```

covering any prescribed disjoint line.  See the
[primary paper, Theorem 4.5](https://combinatorialpress.com/article/ars/Volume%20058/volume-58-paper-27.pdf).

For odd `q>=7`, set `s=(q+1)/2`, so `N=(q+3)/2`.  Regard the conic points as the
three-row parity columns of an `[N,N-3]` GRS code and take `e=2`.  Then

```text
2e=4<N,       e+(N-3)+1=N,       |P(F_q)|=q+1>N.
```

The covered line is disjoint from the conic, hence it is not a support secant.  This gives an
infinite family of exact counterexamples at the boundary `e+k+1=n`.

`Frontier/_HalfRadiusConicSecantBoundaryFamily.lean` formalizes the field-generic algebraic
core of the same phenomenon on a tangent line: uniform affine secant coefficients, distinct
endpoints, the infinity-point secant, and the equality-face arithmetic.  Its hypotheses expose
the finite-field existence step instead of hiding it.

## Surviving target

The refutations retire any argument based only on ordinary MDS, conic/NRC structure, generalized
Hamming weights, unrestricted secant geometry, strict slack, or the low-rate inequality alone.
They do **not** settle the production slice

```text
e=n/2-1,       k<=n/4,       n=2^mu,
```

where the slack `n-(e+k+1)` is at least about `n/4`.  The corrected live question must retain
the conjunction of even two-power length, the fixed two-power evaluation subgroup, and the exact
half-predecessor radius.  The `[8,4]` example shows that dyadicity alone is insufficient, the
`[9,2]` example shows that strict low-rate slack alone is insufficient, and the Ng--Wild family
shows that merely replacing MDS by GRS is also insufficient.
