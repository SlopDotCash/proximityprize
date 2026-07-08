# delta* #466 R207: nonzero Gauss-period dilation consumer

Status: landed as a checked nonprincipal-frequency correction of the concrete dilation bridge.

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R207NonzeroGaussPeriodDilationConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R207NonzeroGaussPeriodDilationConsumer.lean
✅ OK (15s)

./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R207NonzeroGaussPeriodDilationConsumer
Build completed successfully
```

Content:

- Defines `nonzeroFreqs = Finset.univ.erase 0`.
- Proves multiplication by any nonzero `ζ` preserves this carrier.
- Proves the nonprincipal shift identity
  `Σ_{b≠0} exp((1/4) * ‖η_G(ζ*b)‖) = Σ_{b≠0} exp((1/4) * ‖η_G(b)‖)`.
- Wires the actual dilation parent `b ↦ ‖η_{G ∪ ζG}(b)‖` into the R200/R168 shifted-quarter
  prize consumer over the nonzero carrier.

Why this matters:

R204--R206 proved the full-frequency bridge, but the prize object and the in-tree
DC-subtracted moment route are nonprincipal: the `b = 0` DC term must not be part of the
quarter-MGF residual. R207 aligns the shifted-quarter chain with that nonzero-frequency carrier.

Remaining analytic input:

The only load-bearing assumption at this interface is now the nonzero one-child quarter-MGF bound

```text
Σ_{b≠0} exp((1/4) * ‖η_G(b)‖) ≤ 2 * #(b ≠ 0).
```

That remains the BGK / bulk-plus-spikes analytic core, not a tower-bookkeeping issue.
