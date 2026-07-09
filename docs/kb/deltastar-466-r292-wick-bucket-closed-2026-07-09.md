# R292: Wick-perfect bucket is closed form, tending to 6

Date: 2026-07-09.

## Claim

The Wick-perfect-matching part of the R291 constrained sextic expansion is no longer a
mystery term.  For the Jacobi sequence used in R23, the nonzero coefficient set has:

```text
one coefficient with |J|^2 = 1,
r = m - 2 coefficients with |J|^2 = q.
```

The coefficient `j=0` is excluded from the triple convolution, so the remaining small
coefficient is the only degenerate nonzero character.

## Closed formula

Let

```text
W(m,q) = WickPerfectMatching.
```

Then

```text
W(m,q)
  = 1
  + r(6r^2 - 9r + 4) q^3
  + 9r(2r - 1) q^2
  + 9r q,
where r = m - 2.
```

Equivalently, by unordered multiset shape:

```text
all same:       1 + r q^3
two-one:        9(r q + r q^2 + r(r-1) q^3)
all distinct:   36(C(r,2) q^2 + C(r,3) q^3)
```

Normalized by `m^3 q^3`, this tends to `6` as `m,q -> infinity`.

## Probe verification

The optimized R290 probe now computes this closed formula and compares it to the exact
bucket.  Absolute errors are floating-rounding errors against enormous totals:

```text
p=193  n=8  m=24   wick/scale=4.315981  formula_err=2.89e-02
p=577  n=8  m=72   wick/scale=5.396765  formula_err=2.88e+00
p=1153 n=16 m=72   wick/scale=5.396562  formula_err=6.00e+00
p=4129 n=16 m=258  wick/scale=5.827275  formula_err=2.87e+08
```

At `p=4129,m=258`, the scale is about `m^3 q^3`, so `2.87e8` is numerically negligible.

## Consequence

The R23 target

```text
E3 <= C m^3 q^3
```

can now be decomposed as

```text
E3 = W(m,q) + GenericDistinctConnected + CollisionCorrection.
```

Since `W/(m^3 q^3) -> 6`, a constant-scale proof must supply a signed upper bound for
`GenericDistinctConnected` and a small budget for `CollisionCorrection`.  This deletes the
Wick bucket from the analytic unknowns; the only genuine subconvexity is the generic
distinct connected family on the R289 convolution hyperplane.
