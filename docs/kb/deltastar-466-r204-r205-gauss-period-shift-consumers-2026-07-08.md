# delta* #466 R204/R205: Gauss-period shift consumers

Status: landed as checked full-frequency shift consumers.

Artifacts:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R204GaussPeriodShiftQuarterSum.lean`
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R205GaussPeriodShiftPrizeConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R204GaussPeriodShiftQuarterSum.lean
✅ OK (6s)

scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R205GaussPeriodShiftPrizeConsumer.lean
✅ OK (6s)

./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R205GaussPeriodShiftPrizeConsumer
Build completed successfully
```

Content:

- R204 proves the concrete Gauss-period frequency-shift identity
  `Σ_b exp((1/4) * ‖η_G(ζ*b)‖) = Σ_b exp((1/4) * ‖η_G(b)‖)` for any nonzero `ζ`.
- R205 wires that identity into R200/R168. For the dilation-recursion children
  `left b = ‖η_G(b)‖` and `right b = ‖η_G(ζ*b)‖`, the shifted-quarter prize consumer
  now needs only:
  - parent subadditivity against those two children;
  - the one-child quarter-MGF budget for `‖η_G(b)‖`.

Role in the live route:

R202/R203 closed the abstract permutation bookkeeping. R204/R205 instantiate the same idea
for the actual full finite-field frequency set using multiplication by a nonzero scalar.
This discharges the full-frequency child-shift comparison in the dyadic dilation route.

Still open after R205:

- Transfer this full-frequency shift identity to any quotient/subsampled index set used by the
  final tower interface, if the consumer is not run over `Finset.univ`.
- Prove the one-level quarter-MGF bound for the Gauss-period spectrum. This remains the
  analytic BGK/large-tail core, currently routed through the small-direct and large normalized
  bulk-plus-spikes residuals.
