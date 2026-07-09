# R290: signed connected sextic cancellation

Date: 2026-07-09.

## Claim

The R289 constrained sextic average is not a positive diagonal-dominance problem.  Even at
the first small Jacobi cell, the Wick-perfect-matching bucket is larger than the final cubic
energy, and the connected remainder is a signed, load-bearing correction.

The exact constrained six-tuple expansion splits

```text
E3 = WickPerfectMatching + ConnectedRemainder
```

where `WickPerfectMatching` means the left triple `{x,y,z}` is the same multiset as the right
triple `{x',y',z'}`.  At `p=193, n=8, m=24`:

```text
E3/(m^3 q^3)                  =  3.0190
WickPerfectMatching/(m^3 q^3) =  4.3160
ConnectedRemainder/(m^3 q^3)  = -1.2970
```

So a proof that only upper-bounds connected mass by absolute values is structurally pointed in
the wrong direction: the connected part must cancel with the Wick bucket.

## Exact probe output

`scripts/probes/probe_r290_constrained_sextic_average.py --cells 193:8 --lag-check-limit 32`

```text
p=    193 n=  8 m=  24 beta=2.53 E3/scale=3.0190 wick/scale=4.3160 conn/scale=-1.2970 bucket_err=2.65e-01
  lag_hyperplane_err=9.44e-01
  wick_perfect_matching            +4.315981
  connected_L(1, 1, 1)_R(1, 1, 1)  -1.230546
  connected_L(2, 1)_R(2, 1)        -0.174001
  connected_L(1, 1, 1)_R(2, 1)     +0.076668
  connected_L(2, 1)_R(1, 1, 1)     +0.076668
  connected_L(1, 1, 1)_R(3,)       -0.023313
  connected_L(3,)_R(1, 1, 1)       -0.023313
  connected_L(3,)_R(3,)            +0.000495
```

The `bucket_err` and `lag_hyperplane_err` are absolute floating-point errors against a
`3e11` total.

## Sampling caveat

A naive sample of left triples at `p=577, n=8, m=72` is too high-variance for certification:
it recovers the Wick bucket scale but gives a large signed bucket error.  Future probes should
use variance reduction: stratify by the sum `d`, collision shape, and perfect-matching count,
or compute each sum-fiber exactly with FFT batching.

## New hypothesis

The next analytic statement should be:

```text
SignedConnectedSexticCancellation:
  WickPerfectMatching + ConnectedRemainder <= C * m^3 * q^3
```

with the connected term kept as a signed aggregate over the R289 hyperplane.  This is sharper
than both:

1. the quadratic lag route, which spends the zero-lag profile too early;
2. the all-lag R37/R38 route, which spends a five-dimensional supremum before imposing the
   convolution hyperplane.

In geometric language: separate the Wick diagonal strata, then prove cancellation for the
connected six-point family as an aggregate over the convolution surface.  The proof target is
not "connected mass is small"; it is "connected mass has the right signed interference with
the Wick strata."
