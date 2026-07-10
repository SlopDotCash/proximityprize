# Rate-half predecessor: three-core radix counterexample

The proposed all-stack cap at the predecessor of `31/64` is false.  The failure is structural,
occurs in the first certified prize field, and scales exactly to length `2^30`.

Write

```text
n = 64m,  m = 2^24,  k = 32m,  t = 33m+1.
```

Here `t` is the agreement threshold at the predecessor of `31/64`.  On the quotient domain
`mu_64`, choose the three explicit 33-subsets encoded by

```text
542424784538028885
16114235817432360298
3975377171011979844.
```

For a 33-subset `C`, restriction to `C` is a degree-`<32` Reed--Solomon word exactly when its
unique parity check vanishes.  Intersecting the three parity kernels gives a codimension-three
spline space `W`.  For each of the 31 coordinates outside each core, interpolation on the core
defines an external-defect functional on `W/RS_32`.  Exact row reduction modulo the certified
prime

```text
P = 365375409332725729550921208179070755120141565953
```

shows that all `3*31=93` defect functionals are nonzero and pairwise projectively distinct.
In fact coordinate 6 is nonzero in every reduced representative, and the 93 ratios
`coordinate_15/coordinate_6` are pairwise distinct.  Thus one two-coordinate projective chart
certifies the entire base separation; a formal certificate need not compare every vector pair.
`Frontier/_W7RateHalfFingerprintSeal.lean` recomputes the reduced representatives from the
literal domain, core, and row-reduction tables using natural-number modular arithmetic.  Lean's
kernel checks all 186 scalar evaluation facts

```text
reducedDirection_j[6] != 0,
reducedDirection_j[15] / reducedDirection_j[6] = fingerprint_j
```

for `j : Fin 93`, proves the cast bridge into the certified field, and derives projective
separation and the Vandermonde lift without a named hypothesis.  Thus the base fingerprint
certificate is closed.  The remaining construction work is the downstream identification of
these computed defect rows with the literal lifted core/fresh MCA certificates; the counting,
tensor separation, hyperplane avoidance, and field budgets are already kernel-checked.

## Radix lift

Every polynomial of degree `<32m` has the radix form

```text
sum_(b<m) X^b Q_b(X^m),     deg Q_b < 32.
```

Lift each base core to the union of its 33 full `X^m` fibers.  The lifted compatible-word space
is the tensor product of the base spline space with the `m` radix coordinates.  At a point `x`
outside a lifted core, the external defect is

```text
d_C,y tensor (1,x,...,x^(m-1)),     y=x^m.
```

Rank-one tensors are projectively equal only when both factors are projectively equal.  The 93
base directions are distinct, and the `m` Vandermonde vectors above a fixed quotient coordinate
are distinct because their first coordinate is one.  Therefore the lift has exactly

```text
D = 93m = 1,560,281,088
```

projective external-defect directions.  This exceeds the claimed budget

```text
n = 64m = 1,073,741,824
```

by `29m = 486,539,264`.

## Realizing distinct bad scalars

Let the `D` distinct nonzero functionals be `d_j` on the lifted spline quotient.  Since `D<P`, a
vector `u1` exists outside their `D` kernels.  After fixing it, equality of the scalar ratios for
two directions is one proper hyperplane in `u0`:

```text
d_i(u0)d_j(u1) - d_j(u0)d_i(u1) = 0.
```

Because `C(D,2)<P`, another hyperplane-avoidance step chooses `u0` outside every collision
hyperplane.  Thus all

```text
gamma_j = -d_j(u0)/d_j(u1)
```

are distinct.  For direction `(C,x)`, the fold `u0+gamma_j*u1` agrees with the affine combination
of the two core polynomials on the `33m`-point core and at `x`, giving `t=33m+1` agreements.  The
nonzero denominator defect means the second row does not agree there, so the witness is a genuine
`mcaEvent` by `_HalfPredecessorCoreFreshDecode.lean`.

Consequently the first-field predecessor bad count is at least `93m>n`.  The hypothesis of
`firstPrime_rateHalf_deltaStar_eq_thirtyOneSixtyFour_of_predecessor_count` cannot hold.  This does
not solve the original proximity prize; it removes the attempted exact `31/64` pin and exposes a
multi-core construction that should now be optimized toward the real interior threshold.

Reproduce the finite-field certificate with

```text
python3 scripts/probes/probe_rate_half_three_core_radix_counterexample.py
```
