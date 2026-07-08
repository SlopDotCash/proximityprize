# delta* #466 R209: nonzero quarter-MGF residual consumer

Status: landed as a checked interface cleanup.

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R209NonzeroQuarterMGFResidualConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R209NonzeroQuarterMGFResidualConsumer.lean
✅ OK (11s)

./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R209NonzeroQuarterMGFResidualConsumer
Build completed successfully
```

Content:

- Defines the remaining analytic input as
  `NonzeroQuarterMGFResidual ψ G :=
   MGFBound nonzeroFreqs (fun b => ‖η_G(b)‖) 2 (1/4)`.
- Proves this named residual unfolds to R207's raw nonzero quarter-MGF sum budget.
- Wires the named residual into both the dyadic-tail and prize-square R207 endpoints.

Why this matters:

R207 aligned the shifted-quarter chain with the nonprincipal carrier `b ≠ 0`.
R209 aligns the remaining hypothesis with the existing S11 concentration API:
the hard analytic input is now a single named `MGFBound`, not an ad hoc summation
assumption.

Remaining work:

Prove `NonzeroQuarterMGFResidual ψ G` uniformly for the prize Gauss-period spectra.
This is the surviving BGK/survival-tail problem.
