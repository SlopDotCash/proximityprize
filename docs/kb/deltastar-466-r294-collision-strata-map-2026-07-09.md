# R294: collision strata map; the old cube split is too coarse

Date: 2026-07-09.

## Claim

The R41/R57/R60 cube-vs-generic split is not the right interface for the R293 collision
correction.

R41 isolates only the single shape

```text
(a,b,a',b') = (0,0,0,0),
```

the cube-cube class where both triples have internal partition `(3)`.  R293's collision
correction is much larger as a shape set: it contains every connected repeated-index bucket
on the R289 hyperplane after the closed Wick-perfect terms have been removed.

The repeated-index collision correction should therefore be split as lower-dimensional
strata, not as cube-vs-noncube:

```text
Coll =
  Coll_(3,3)
+ Coll_(3,21)
+ Coll_(21,3)
+ Coll_(21,21)
+ Coll_(3,111)
+ Coll_(111,3)
+ Coll_(21,111)
+ Coll_(111,21).
```

Here `(111)` denotes the fully distinct side, `(21)` a side with exactly one repeated index,
and `(3)` the all-equal side.  The fully distinct connected bucket
`connected_L(111)_R(111)` is deliberately excluded; that is the R293 load-bearing generic
term.

## Why this matters

The older cube route spends an all-lag pointwise sextic budget and then uses triangle scale
for the cube lag.  That was useful for modularizing R38, but it is orthogonal to the current
constrained signed average:

```text
3t + a + b = a' + b'.
```

The R293 target only needs a signed or absolute budget for the residual repeated-index
correction on this hyperplane.  Most repeated-index buckets reduce the six-point family to
four- or five-point families, so they should be approachable through lower-dimensional
Jacobi-lag inputs rather than the full R38 sextic wall.

## New interface

The Lean socket `_R294CollisionStrataMapSocket.lean` records:

* the eight collision buckets listed above;
* their exact sum as the collision correction;
* a budget consumer turning per-stratum estimates into the R293 `CollisionBudget`;
* a marker that the old cube split covers only the `(3,3)` bucket.

This leaves the proof frontier in the right shape:

```text
closed Wick bucket
+ generic fully distinct connected six
+ lower-dimensional collision strata.
```

The next mathematical task is to prove a uniform lower-dimensional budget for those eight
strata on the R289 hyperplane, then return to the main generic-distinct subconvexity theorem.
