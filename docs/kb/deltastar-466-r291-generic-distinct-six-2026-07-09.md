# R291: generic distinct-six bucket is the signed sextic core

Date: 2026-07-09.

## Claim

After R289's convolution hyperplane and R290's signed Wick/connected split, the main connected
mass is concentrated in the fully distinct six-point bucket:

```text
connected_L(1,1,1)_R(1,1,1).
```

The repeated-index collision buckets are visible but much smaller in the larger exact cells.
Thus the sharp subconvexity target is the generic distinct-six connected family, with collision
strata treated as lower-order corrections.

## Exact data

All data below comes from the exact per-sum/collision-shape aggregation in
`scripts/probes/probe_r290_constrained_sextic_average.py`.

```text
p=193 n=8 m=24 beta=2.53
E3/scale   =  3.0190
Wick/scale =  4.3160
Conn/scale = -1.2970
distinct-connected/scale = -1.2305

p=577 n=8 m=72 beta=3.06
E3/scale   = 13.9699
Wick/scale =  5.3968
Conn/scale = +8.5731
distinct-connected/scale = +8.6615

p=1153 n=16 m=72 beta=2.54
E3/scale   =  5.1654
Wick/scale =  5.3966
Conn/scale = -0.2312
distinct-connected/scale = +0.3312

p=4129 n=16 m=258 beta=3.00
E3/scale   = 18.9503
Wick/scale =  5.8273
Conn/scale = +13.1230
distinct-connected/scale = +12.6086
```

Here `scale = m^3 q^3`.  The `m=258` cell has absolute bucket error `6.84e6`, but this is
negligible relative to `scale`.

## Interpretation

The Wick-perfect-matching bucket sits near `~5-6` in these cells.  The final constant is then
mostly selected by the generic distinct connected bucket, whose sign and size vary with the
arithmetic cell.  The repeated-index buckets are correction terms:

* `L(2,1)_R(2,1)` is small by `m=258`;
* mixed `L(1,1,1)_R(2,1)` and transpose can matter at `m=72`, but are still secondary;
* triple-collision buckets are tiny.

So the next hypothesis should not average all connected terms indiscriminately.  It should split

```text
E3 = WickPerfectMatching
   + GenericDistinctConnected
   + CollisionCorrection
```

and prove:

```text
WickPerfectMatching + GenericDistinctConnected <= C0 * m^3 q^3,
CollisionCorrection <= C1 * m^3 q^3 with small C1 or lower-order decay.
```

## Proof target

In R37 coordinates, the generic bucket corresponds to lag data for which both triples
`(j+t, j+t+a, j+t+b)` and `(j, j+a', j+b')` have three distinct entries and are not the same
multiset, while still satisfying the R289 hyperplane

```text
3t + a + b = a' + b'.
```

This is the natural place for a Katz/Sato-Tate or sheaf-theoretic connected-family theorem:
the diagonal Wick classes are removed, repeated-index strata are lower-dimensional, and the
remaining generic family is the piece controlling the observed constant.
