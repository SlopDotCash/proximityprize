# Issue #466 R369: signed difference-mass doubling

Date: 2026-07-09

## Result

R369 extends R321's autocorrelation identity from kernel relations to every nonzero shadow
difference:

```text
allShadowDifferenceMass(d) = NR(2m,m,2r,d).
```

Consequently the exact centered discrepancy is

```text
sum_{d != 0} NR(2m,m,2r,d) * (q * 1[eval_g(d)=0] - 1),
```

where the sum ranges over realized doubled-walk endpoints. Both results are axiom-clean.

## Significance

The sharp R322 endpoint factorial envelope now applies to every term of the corrected signed
decomposition, not only its positive kernel terms. The unresolved deep theorem is therefore a
weighted discrepancy estimate for evaluation on the finite family of doubled-walk endpoints,
with completely explicit characteristic-zero weights.
