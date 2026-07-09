# Issue #466 R378: signed difference rotation invariance

Date: 2026-07-09

## Result

For the negacyclic shadow rotation `rotZ`, R378 proves

```text
differenceDiscrepancyCoeff(rotZ d) = differenceDiscrepancyCoeff(d)
NR(2m,m,2r,rotZ d) = NR(2m,m,2r,d)
signedEndpointSummand(rotZ d) = signedEndpointSummand(d).
```

The result uses R371's kernel stability and R372's histogram equivariance. It is axiom-clean.

## Significance

Every term in R369's signed endpoint discrepancy is constant on its rotation orbit. The remaining
quantitative combinatorial target is to lower-bound the orbit size of an endpoint with
`L1 <= 2r`; sparsity suggests an orbit of size at least `m/(2r)`. Such an orbit factor would give
the signed prime-ideal discrepancy a genuine dimension saving unavailable to raw relation counts.
