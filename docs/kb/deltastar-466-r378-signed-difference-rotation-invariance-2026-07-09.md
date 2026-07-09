# Issue #466 R378: signed difference rotation invariance

Date: 2026-07-09

## Result

For the negacyclic shadow rotation `rotZ`, R378 proves

```text
differenceDiscrepancyCoeff(rotZ d) = differenceDiscrepancyCoeff(d)
```

The result uses R371's kernel stability and is axiom-clean.

## Significance

The positive/negative coefficient in R369's signed discrepancy is constant on each rotation
orbit. Histogram-mass invariance would make the complete summand invariant, but the currently
landed R372 source fails fresh compilation and must be repaired before that stronger weld is used.
Afterward, the quantitative target is an orbit-size lower bound for `L1 <= 2r`, expected at
`m/(2r)`.
