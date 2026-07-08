# #466 R211: nonzero normalized-square dilation consumer

Date: 2026-07-08

## What landed

Added `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R211NonzeroNormalizedSqDilationConsumer.lean`.

The file corrects the live dyadic MGF bridge to the variance-normalized squared
Gauss-period statistic used by the probes:

```text
X_G(b) = ‖η_G(b)‖² / σ²,   b ≠ 0.
```

For a disjoint dilation step `G ∪ ζG`, Lean now proves the deterministic parent
inequality

```text
‖η_{G∪ζG}(b)‖² / (2σ²)
  ≤ ‖η_G(b)‖² / σ² + ‖η_G(ζb)‖² / σ².
```

The same file proves the nonzero-carrier shifted quarter-MGF identity for the
normalized-square child spectrum and packages both facts through the existing
R200 shifted-quarter consumer.

## Why this matters

R207/R209 named a raw-norm nonzero residual.  That residual is honest but
over-strong for the prize route and does not match the numeric probes, whose
`normalized_values_vectorized` routine computes `|η|² / σ²`.  R211 puts the
formal bridge back on the probe-aligned object:

```text
MGFBound (b ≠ 0) (fun b => ‖η_G(b)‖² / σ²) 2 (1/4).
```

The open analytic core is therefore no longer hidden in a scale mismatch.  It is
exactly the nonzero normalized-square quarter-MGF bound.

## Verification

Fast cone check:

```bash
scripts/pg-iterate.sh -q \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R211NonzeroNormalizedSqDilationConsumer.lean
```

Result:

```text
OK (21s)
```

## Residual

Prove or refute the nonzero normalized-square quarter-MGF bound uniformly for
the relevant dyadic subgroup tower:

```text
∑_{b≠0} exp((1/4) · ‖η_G(b)‖² / σ²) ≤ 2 · #{b : b ≠ 0}.
```

The R190/R210 bulk-plus-spikes machinery should now be re-specialized to this
normalized-square object rather than the raw norm.
