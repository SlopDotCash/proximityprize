# delta* #466 R206: Gauss-period dilation prize consumer

Status: landed as a checked concrete dilation-recursion bridge.

Artifact:

- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R206GaussPeriodDilationPrizeConsumer.lean`

Checks:

```text
scripts/pg-iterate.sh -q ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R206GaussPeriodDilationPrizeConsumer.lean
✅ OK (6s)

./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._R206GaussPeriodDilationPrizeConsumer
Build completed successfully
```

Content:

- `dyadicTailMGF_of_gaussPeriod_dilation_quarter`: for the actual dilation parent
  `b ↦ ‖η_{G ∪ ζG}(b)‖`, the R168 dyadic-tail residual follows from the one-child
  quarter-MGF bound for `b ↦ ‖η_G(b)‖`.
- `prize_sq_of_gaussPeriod_dilation_quarter`: the same concrete dilation parent wired
  to the prize-square endpoint.

What R206 removes:

R205 still exposed the abstract inequality

```text
parent b ≤ ‖η_G(b)‖ + ‖η_G(ζ*b)‖.
```

R206 discharges it using the existing theorem `eta_union_dilate_norm_le`, assuming the
dilate is disjoint from the base set.

Still open after R206:

- The one-child quarter-MGF bound for `b ↦ ‖η_G(b)‖`.
- In the current route this is still the analytic bulk-plus-spikes / BGK-style residual,
  not a bookkeeping or tower-composition issue.
