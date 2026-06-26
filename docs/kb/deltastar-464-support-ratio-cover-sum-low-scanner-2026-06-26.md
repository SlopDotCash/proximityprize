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
supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
```

The first theorem is the local high-profile estimate.  It does not need the global `k <= a`
threshold used by the older exact-threshold cover bound; it only needs `k <= S.card`.

The second theorem is the pure extractor: any cover-sum overflow under the high-envelope condition
has a low-profile overflow.  The third theorem plugs this into the uniform production scanner, so a
failed bad-scalar budget now returns either zero-direction saturation or a large-zero safe low
cover-sum witness.

## Consequence

The support-ratio cover-sum route is now aligned with the other low-profile scanners.  High
profiles are no longer part of the residual once the envelope pays the explicit
`|F| * choose(#support, a - t)` cost.  Any future improvement has to beat the finite cover sum in
the low range `t < k`, where RS uniqueness alone does not collapse the coordinate fibers.
