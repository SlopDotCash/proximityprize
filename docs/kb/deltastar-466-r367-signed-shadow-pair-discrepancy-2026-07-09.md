# Issue #466 R367: signed shadow-pair discrepancy

Date: 2026-07-09

## Result

R367 proves that all ordered distinct shadow pairs have total weight

```text
n^(2r) - shadowEnergy.
```

It then rewrites R366's relation anomaly exactly as

```text
sum_{v != w} NR(v) NR(w) * (q * 1[eval(v)=eval(w)] - 1).
```

Thus colliding pairs contribute `(q-1) NR(v)NR(w)` and non-colliding pairs contribute
`-NR(v)NR(w)`. The equality is axiom-clean.

## Significance

This restores the cancellation erased by raw kernel-relation counting. The deep prize wall is a
signed discrepancy estimate for the evaluation map on the characteristic-zero shadow-pair
measure. Any successful lattice, transfer-operator, or expander argument must control this signed
sum; proving that the positive kernel support is small is neither true nor necessary after the DC
crossover.
