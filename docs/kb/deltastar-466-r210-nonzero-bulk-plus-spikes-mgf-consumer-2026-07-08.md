# delta* #466 R210: nonzero bulk-plus-spikes MGF consumer

Status: landed as a checked specialization of R190 to the nonprincipal Gauss-period spectrum.

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R210NonzeroBulkPlusSpikesMGFConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R210NonzeroBulkPlusSpikesMGFConsumer.lean
✅ OK (10s)

./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R210NonzeroBulkPlusSpikesMGFConsumer
Build completed successfully
```

Content:

- `nonzeroQuarterMGFResidual_of_bulkPlusSpikesGridTail`: arbitrary constants.
- `nonzeroQuarterMGFResidual_of_threeFifths_plus_two_gridTail`: the live `(3/5, 2)` constants.

Meaning:

The named residual `NonzeroQuarterMGFResidual ψ G` now follows from:

- a threshold grid `Θ`;
- nonnegative staircase increments `δ`;
- staircase domination of `exp(‖η_G(b)‖/4)` on `b ≠ 0`;
- nonzero survival-count tail
  `#{b≠0 : θ ≤ ‖η_G(b)‖} ≤ (3/5) * #(b≠0) * exp(-θ/2) + 2`;
- the corresponding weighted grid budget.

Remaining work:

Prove that nonprincipal bulk-plus-spikes survival envelope and its finite grid budget uniformly
for the prize Gauss-period spectra.
