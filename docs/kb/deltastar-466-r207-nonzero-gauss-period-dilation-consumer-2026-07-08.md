# delta* #466 R207: nonzero Gauss-period dilation consumer

Status: landed as a checked nonprincipal-frequency correction of the concrete dilation bridge.

Artifact:

- `Research/ProximityPrize/Frontier/_R207NonzeroGaussPeriodDilationConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q Research/ProximityPrize/Frontier/_R207NonzeroGaussPeriodDilationConsumer.lean
✅ OK (15s)

./scripts/lake-locked.sh build Research.ProximityPrize.Frontier._R207NonzeroGaussPeriodDilationConsumer
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

**Correction (2026-10-28 audit, T48; see R-079).** Removing DC was the right repair, but this
particular raw-amplitude bound is not an open core. It is infeasible at the intended growing `n`,
and no numerical FFT is needed to see it. Since `exp(x/4) ≥ 1 + x²/32` for `x ≥ 0`, and nonzero
Parseval gives `Σ_{b≠0} ‖η_G(b)‖² = n(q − n)`, the left side is at least
`(q − 1) + n(q − n)/32`. A bound by `2(q − 1)` therefore forces `n(q − n) ≤ 32(q − 1)`. That fails
for every `n ≥ 33` with `q ≥ n²`, because then `(n − 32)q − n² + 32 ≥ (n − 33)n² + 32 > 0`. For the
actual subgroup `μ₆₄ ⊆ F₂₅₇` the two sides are `12352 > 8192`, and the exponential sum is at least
`642`, above the proposed ceiling `512` (audit evidence `quarter-mgf-normalization-check.json`).
The normalized-square and nonzero corrected MGF routes (for example R217's carrier) are different
objects and are not refuted by this. The arbitrary-scale conditional consumers proved here remain
valid. No production pin follows from this interface.
