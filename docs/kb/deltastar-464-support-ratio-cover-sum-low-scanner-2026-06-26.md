# delta* #464: support-ratio cover-sum low scanner

Date: 2026-06-26.

Status: structural scanner; not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The support-ratio cover-sum route already exposed a finite obstruction:

```text
sum_gamma sum_T #coordinateAgreementFiber(u0 + gamma * u1, S union T) > M(t).
```

The new low scanner separates the high zero profiles from the hard low interpolation range.
If `S` already has at least `k` coordinates, every coordinate-agreement fiber in the cover sum is
singleton-bounded by Reed--Solomon uniqueness.  Hence the whole finite cover sum is bounded by

```text
|F| * choose(#directionSupportSet(u1), a - #S).
```

Therefore, whenever the proposed envelope `M(t)` dominates this scalar-times-support-binomial
ceiling for every high profile `k <= t < a`, an overfull cover-sum witness must have `t < k`.

## Lean Surface

`LineListSupportRatioFiber.lean` now records:

```lean
ZeroLowSupportRatioCoverSumBudgeted
UniformLargeZeroSafeLowSupportRatioCoverSumBudgeted
ZeroLowSupportRatioHeavyCoordinateFiberBudgeted
UniformLargeZeroSafeLowSupportRatioHeavyCoordinateFiberBudgeted
supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
zeroSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_low_and_high_one
zeroSupportRatioCoverSumBudgeted_of_low_and_high_choose
uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_low_and_high_choose
not_zeroLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
not_uniformLargeZeroSafeLowSupportRatioHeavyBudgeted_iff_exists_low_fiber_gt
not_zeroLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
not_uniformLargeZeroSafeLowSupportRatioCoverSumBudgeted_iff_exists_low_coverSum_gt
zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyCoordinateFiberBudgeted
uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
not_zeroLowSupportRatioHeavyBudgeted_of_not_zeroLowExactAppearingBudgeted
not_uniformLowSupportRatioHeavyBudgeted_of_not_uniformLowExactAppearingBudgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavyCoordFibers
exists_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums
exists_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
```

The first theorem is the local high-profile estimate.  It does not need the global `k <= a`
threshold used by the older exact-threshold cover bound; it only needs `k <= S.card`.

The second theorem is the pure extractor: any cover-sum overflow under the high-envelope condition
has a low-profile overflow.  The third theorem plugs this into the uniform production scanner, so a
failed bad-scalar budget now returns either zero-direction saturation or a large-zero safe low
cover-sum witness.

Follow-up: the positive split is now named too.  A caller can prove the finite cover-sum budget
only for low profiles `t < k`, separately prove the high-profile envelope
`|F| * choose(#support, a - t) <= M(t)` for `k <= t < a`, and then feed
`uniformLineBadScalarsBudgeted_of_lowSupportRatioCoverSums`.  The negated low-budget iff gives the
matching finite obstruction: an overfull low profile is exactly the failure of the low-cover
assumption.  With the support-side production, zero-direction safety, arithmetic fit, and
high-profile cover-sum ceiling fixed,
`exists_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted` gives the
same witness directly from failed bad-scalar production.

The support-ratio-heavy coordinate-fiber route now has the same positive split.  Low heavy fibers
are the only nontrivial estimates; high heavy fibers are bounded by one via RS uniqueness, so the
high envelope is just `1 <= M(t)` for `k <= t < a`.

The low support-ratio-heavy socket also feeds the low exact-appearance socket directly.  Thus a
failed low exact-appearance budget is not a separate residual: by the contrapositive wrappers, it
already refutes the sharper low support-ratio-heavy budget.

## Consequence

The support-ratio cover-sum route is now aligned with the other low-profile scanners.  High
profiles are no longer part of the residual once the envelope pays the explicit
`|F| * choose(#support, a - t)` cost.  Any future improvement has to beat the finite cover sum in
the low range `t < k`, where RS uniqueness alone does not collapse the coordinate fibers.  The
heavy-fiber variant makes the same residual even sharper: once high profiles pay only one, any
remaining failure must be a low support-ratio-heavy fiber.
