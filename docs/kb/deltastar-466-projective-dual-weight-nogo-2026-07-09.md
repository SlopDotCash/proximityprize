# Projective dual-weight route: exact interface and no-go

Date: 2026-07-09
Issue: #466

## Result

`Frontier/_ProjectiveDualWeightNoGo.lean` adds the exact matroid interface for the proper-ball
reduction.  If `P` is a genuine rank-two quotient pencil and a normalized slot is bad, then some
admissible support subspace `B_S` satisfies

```text
slot in P inter B_S,
finrank(P inter B_S) = 1.
```

The equality is forced by three facts already present in the proper-ball dictionary: the slot is
nonzero, `finrank P = 2`, and `P` is not contained in `B_S`.  The theorem is
`badSlot_witnesses_rankOne_supportIntersection`.

This identifies what a dual-weight or matroid argument would have to count: not merely the first
support size at which intersection rank one or two occurs, but the number of distinct rank-one
intersections produced by all admissible supports.

## Parametric no-go

The theorem `orderTwoHigherMDS_not_linearMCA_of_choose_gt` applies the generic quotient
interpolation spread to the same smooth Reed--Solomon code whose Vandermonde generator frame is
certified by `reedSolomonFrame_isHigherMDS_two`.  Under its explicit field/order hypotheses, if

```text
choose(s,r) > K * (s*m),
```

then the code is an actual length-`s*m`, dimension-`(r-1)m` smooth-domain RS code, its frame is
higher-MDS of order two, and nevertheless

```text
epsMCA(radius = 1-r/s) > K * (s*m) / p.
```

The fully concrete theorem `f4129_orderTwoHigherMDS_not_lengthBound` takes
`(p,s,m,r,K) = (4129,8,1,3,1)`: the length-eight, dimension-two smooth RS frame is order-two
higher-MDS, while its MCA numerator is at least `choose(8,3)=56 > 8` at radius `5/8`.

## Verdict

Ordinary MDS data, its minimum/generalized-weight thresholds, or order-two generic-intersection
data cannot alone provide the required linear projective census.  Those invariants control when a
support intersection first becomes nonzero or two-dimensional; they do not control how many
different one-dimensional intersections occur.

This does **not** refute higher-order (`>= 3`) GM-MDS information or smooth-domain arithmetic.
Any viable dual/matroid route must add a multiplicity theorem for the rank-one intersections,
using structure absent from ordinary/order-two MDS.  The interpolation-spread construction is the
test case that such a theorem must distinguish.

## Validation

The four exported theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.
The file passes the proximity single-file Lean workflow with `autoImplicit = false` declared in
the source.
