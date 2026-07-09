# Issue #466 R380: concrete sparse rotation orbit

Date: 2026-07-09

## Result

R380 defines the first-`m` negacyclic rotation orbit and proves that the orbit of every nonzero
integer vector covers every coordinate. Combining this with R378 and R379 gives

```text
m <= card(rotationOrbit d) * endpointL1(d).
```

Hence a doubled-walk endpoint of `L1 <= 2r` has at least `m/(2r)` distinct rotations. The theorem
is also exported directly in denominator-cleared form `m <= card(orbit) * (2r)`. All results are
axiom-clean.

## Significance

Every member of the orbit has the same signed discrepancy contribution by R378. Therefore every
nonzero signed endpoint occurs in a mass/sign-coherent block of size at least `m/(2r)`. This is a
genuine ambient-dimension saving for the centered prime-ideal discrepancy and formalizes the
rotation quantization observed in the finite censuses.
