# #466 R320: kernel-relation L1 sparsity

## Result

`Frontier/_R320KernelRelationL1Sparsity.lean` strengthens R314's coordinate-height estimate.
It defines the integer `L1` mass

```text
shadowL1(d) = sum_j |d_j|
```

and proves:

```text
shadowL1(vecOf(a)) <= 1,
shadowL1(tupleVec(t)) <= r,
shadowL1(tupleVec(u)-tupleVec(t)) <= 2r.
```

Therefore every realized finite-field kernel relation satisfies

```text
sum_j |d_j| <= 2r,
|support(d)| <= 2r.
```

The corresponding R315 polynomial

```text
P_d(X) = sum_j d_j X^j
```

has exactly the same coefficient `L1` mass on its degree range, hence also at most `2r`.

## Significance

At the prize saddle `r` is about `log p`, while the polynomial degree is `m=n/2`.  R320
replaces the generic picture of an `m`-coordinate box by a polynomial with only `O(log p)`
total signed coefficient mass and at most `O(log p)` occupied exponents.  This is the relevant
regime for sparse cyclotomic resultants and inverse Littlewood--Offord arguments.

The generic FS3 resultant height still raises `2r` to a power proportional to `m`, so R320
alone does not close the fixed-prime count.  The next arithmetic target is a bound or inverse
classification for prime divisors `p == 1 mod 2m` of cyclotomic norms of these sparse
polynomials, weighted by `shadowRelationMass`.

## Validation

```text
./scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R320KernelRelationL1Sparsity.lean
```

passed on 2026-07-09 with no `sorryAx`.
