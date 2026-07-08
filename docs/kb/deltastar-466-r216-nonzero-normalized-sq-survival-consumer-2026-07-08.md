# δ* #466 — R216 nonzero normalized-square survival consumer

R213 names the live analytic socket as

```text
MGFBound (b ≠ 0) (fun b => ‖η_G(b)‖² / σ²) 2 (1/4).
```

R216 specializes the existing S11 finite layer-cake/count-ceiling bridge
directly to that socket.  The remaining proof can now be stated as a concrete
finite-grid survival certificate:

```text
#{b ≠ 0 : θ ≤ ‖η_G(b)‖² / σ²} ≤ B(θ)
Σ_θ δ(θ) B(θ) ≤ 2 · #{b : b ≠ 0}.
```

It also packages the empirically supported half-rate envelope from the R206/R213
probes:

```text
B(θ) = (3/5) · #{b : b ≠ 0} · exp(-θ/2) + 2.
```

This is not a proof of the tail law.  It is the exact Lean-facing endpoint for
turning the observed normalized-square survival law into the R213 quarter-MGF
residual.

Verification:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R216NonzeroNormalizedSqSurvivalConsumer.lean
```

Result:

```text
OK (7s)
```
