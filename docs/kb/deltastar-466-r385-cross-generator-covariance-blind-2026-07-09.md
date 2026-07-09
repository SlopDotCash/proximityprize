# Issue #466 R385: cross-generator covariance blind spot

Date: 2026-07-09

For an endpoint with primitive-generator root count `Z(d)`, R385 proves

```text
offDiagonalPairIncidence(d) = Z(d) * (Z(d) - 1).
```

Hence all `Z(d)=1` endpoints are invisible to every estimate restricted to two distinct
generators. Their centered coefficient remains `q-phi(n)`, which is nonzero and large at prize
scaling. The exact R383 census found that the one-root stratum dominates every tested non-hostile
cell.

Consequently a Weil/Deligne estimate for simultaneous vanishing at two distinct primitive
generators cannot by itself control the centered discrepancy. It still requires a first-incidence
bound for the unique-root stratum, which is the original DC-subtracted energy problem.
