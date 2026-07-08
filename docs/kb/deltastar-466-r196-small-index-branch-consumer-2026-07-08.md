# #466 R196: small-index branch consumer

Status: deterministic consumer plus exact finite-census evidence.

R196 rerun:

```text
R196 small-index base census: tested=75 target=0.199786
violations_target=38
worst_ratio=0.719919 budget=1.338932 mgf1/4=1.292456 maxX=1.458123 M=2 n=8 p=17
worst_budget=2.094093
```

Interpretation:

- The large-index spike-ratio target is false for many tiny quotient sizes `M < 32`.
- This is not a product-MGF obstruction: every directly measured `MGF(1/4)` in the finite census
  remains below `2`.
- Therefore the proof should not try to make the R194 logarithmic max envelope cover small `M`.

Lean consumer:

`_R196SmallIndexBranchConsumer.lean` exposes the proof architecture:

```text
SmallIndexQuarterMGFCertificate s t
  OR
LargeIndexQuarterMGFEnvelope s t
---------------------------------
DyadicQuarterMGFBound s t
```

and feeds that branch into the R188/R168 tower consumer for the parent MGF.

Final shape of this route:

1. finite-certify `M < 32` direct quarter-MGF cases;
2. prove the large-index envelope for `M >= 32` using R189/R194/R195;
3. combine via R196 and feed R191/R188/R168.

The route remains open, but the finite-base obstruction is now correctly isolated rather than
being folded into a false uniform spike-ratio claim.
