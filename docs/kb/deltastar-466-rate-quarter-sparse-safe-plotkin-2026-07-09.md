# Rate-quarter sparse safe lines via constant-weight Plotkin (2026-07-09)

Status: axiom-clean support-at-most-two closure for the `n=16`, `k=4`,
agreement-nine line-list branch.  This is not a full rate-quarter or delta-star
pin.

## Exact diagonal bound

`Frontier/_ConstantWeightPlotkinBound.lean` proves that a constant-weight
family `S_i` of `t`-subsets of a `v`-point universe, with distinct pair
intersections at most `lambda`, satisfies

```text
M * (t^2 - v*lambda) <= v * (t-lambda).
```

The proof keeps the diagonal contribution equal to `t`.  This replaces the
older `v^2` numerator by the sharp `v*(t-lambda)` numerator.  The divided form
also handles an empty family without a separate downstream case split.

## Punctured RS application

For a zero-direction-safe `RS[16,4]` line at agreement threshold `9`, the
witness split puts every appearing codeword in a zero-agreement stratum.  Its
trace is a constant-weight subset of the actual zero-coordinate subtype, and
two distinct traces meet in at most `k-1=3` coordinates.  Plotkin gives:

| direction support | zero-set size | stratum `t` | stratum cap | scalar weight |
|---:|---:|---:|---:|---:|
| 1 | 15 | 8 | 3 | 1 |
| 2 | 14 | 7 | 8 | 1 |
| 2 | 14 | 8 | 3 | 2 |

`Frontier/_HalfPredecessorRateQuarterSparseSafeLine.lean` regroups the exact
punctured line weight and proves the endpoints

```text
support 0: #badScalars = 0
support 1: #badScalars <= 3
support 2: #badScalars <= 8 + 2*3 = 14.
```

Hence every zero-safe direction of support at most two is strictly below the
target budget `16`.

## Boundary

The zero-safety hypothesis is essential: an unsafe line has field-size bad
scalar count by the existing saturation theorem.  The constant-weight
argument also stops honestly at support three.  Its lowest surviving stratum
has `(v,t,lambda)=(13,6,3)`, for which

```text
t^2 - v*lambda = 36 - 39 < 0.
```

Thus the positive Plotkin denominator disappears exactly there.  Closing the
support-three-and-higher safe branch needs additional Reed--Solomon fit
geometry, not more arithmetic rearrangement of the pair-intersection bound.
