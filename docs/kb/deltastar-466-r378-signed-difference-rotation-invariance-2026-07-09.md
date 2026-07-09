# Issue #466 R378: signed difference rotation invariance

Date: 2026-07-09

## Result

For the negacyclic shadow rotation `rotZ`, R378 proves

```text
differenceDiscrepancyCoeff(rotZ d) = differenceDiscrepancyCoeff(d)
NR(2m,m,2r,rotZ d) = NR(2m,m,2r,d)
endpointL1(rotZ d) = endpointL1(d)
signedEndpointSummand(rotZ d) = signedEndpointSummand(d).
```

The result uses R371's kernel stability and the repaired R372 histogram equivariance. It is
axiom-clean from source, without stale object files.

## Significance

Every term in R369's signed endpoint discrepancy is constant on its rotation orbit. The remaining
quantitative target is an orbit-size lower bound for `L1 <= 2r`, expected at `m/(2r)`.
