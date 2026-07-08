# δ* #466 — R218 nonzero survival-to-prize endpoint

R218 composes the exact remaining concentration socket with the corrected
nonprincipal prize endpoint.

Inputs:

```text
NonzeroNormalizedSqGridTail ψ G σ Θ B
∀ b ≠ 0, exp((1/4) * ‖η_G(b)‖² / σ²)
  ≤ Σ_{θ∈Θ, θ≤‖η_G(b)‖²/σ²} δ(θ)
Σ_θ δ(θ) B(θ) ≤ 2 * #(b ≠ 0)
```

Output: the R168/S11 squared prize bound for the concrete normalized dilation
parent

```text
b ↦ ‖η_{G ∪ ζG}(b)‖² / (2σ²),  b ≠ 0.
```

This composes:

* R216's survival/count layer-cake specialization to R213;
* R217's nonzero one-child square-MGF dilation endpoint.

Verified command:

```text
./scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R218NonzeroSurvivalToPrizeEndpoint.lean
```

Output:

```text
'ArkLib.ProximityGap.Frontier.R218NonzeroSurvivalToPrizeEndpoint.prize_sq_of_nonzero_normalizedSq_survival_count_ceiling' depends on axioms: [propext,
OK (19s) — ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R218NonzeroSurvivalToPrizeEndpoint.lean
```

Readout: the remaining analytic wall can now be attacked as a literal finite
survival-grid theorem for the nonzero normalized-square child spectrum.  Once
that grid tail and its weighted budget are proved, this endpoint carries it all
the way to the concrete prize-square inequality.
