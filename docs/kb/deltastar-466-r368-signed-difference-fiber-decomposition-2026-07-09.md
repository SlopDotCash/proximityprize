# Issue #466 R368: signed difference-fiber decomposition

Date: 2026-07-09

## Result

R368 groups the signed pair discrepancy by every characteristic-zero shadow difference `d`.
Writing `M(d)` for its full autocorrelation mass, it proves

```text
signedShadowPairDiscrepancy
  = sum_d M(d) * (q * 1[eval_g(d)=0] - 1).
```

Thus kernel differences have coefficient `q-1`, while non-kernel differences have coefficient
`-1`. The equality is axiom-clean.

## Significance

This is the corrected shell decomposition for the deep wall. R314's kernel-only decomposition is
appropriate for raw collision mass but cannot express DC cancellation. R368 retains the complete
ambient difference measure, allowing endpoint-length and factorial envelopes to be combined with
a signed finite-field discrepancy estimate. A viable prime-ideal argument must control this full
signed sum, rather than bound only its positive kernel support.
