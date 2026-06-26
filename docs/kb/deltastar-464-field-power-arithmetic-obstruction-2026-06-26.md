# DeltaStar #464: field-power arithmetic obstruction

## Context

The coordinate-fiber route closed the raw Reed-Solomon interpolation count:

```text
#coordinateAgreementFiber(S) <= |F|^(k - #S).
```

That theorem is useful because it removes one ambiguity from the large-zero branch.  The remaining
question is no longer whether an RS fiber over `t` prescribed coordinates can be counted.  It can.
The question is whether the resulting weighted binomial sum is small enough for the target
bad-scalar budget:

```text
sum_{t<a} choose(#zeroSet(u1), t) * |F|^(k-t) * support(u1)/(a-t) <= B.
```

The latest formalization shows that this naive field-power envelope is arithmetically too blunt in
large regions of parameter space.

## New Lean Surface

`LineListReduction.lean` now exposes per-summand obstruction lemmas:

```lean
zeroCoordinateAgreementFiberBudgetFits_term_le
fieldPowCoordinateAgreementFiberBudgetFits_term_le
uniformFieldPowCoordinateAgreementFiberBudgetFits_term_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_term_gt
fieldPowCoordinateAgreementFiberBudgetFits_choosePow_le_of_support_ge_sub
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_choosePow_gt
```

The new module `LineListArithmeticObstruction.lean` adds the parameterized direction constructor and
the parameter-only obstruction:

```lean
exists_direction_zero_card_eq_support_card_eq
not_fieldPowFiberFit_of_zeroCount_choosePow_gt
exists_largeZero_direction_support_ge_of_two_mul_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le
```

The constructor is elementary but load-bearing.  For any `z <= n`, choose exactly `z` coordinates
where the direction is zero and put value `1` elsewhere.  Then:

```text
#directionZeroSet(u1) = z
#directionSupportSet(u1) = n - z.
```

Consequently, if `a <= z` the direction is in the large-zero branch.  If also `a - t <= n - z`,
then the `t` summand has support denominator at least one.  The field-power arithmetic fit would
force:

```text
choose(z,t) * |F|^(k-t) <= B.
```

So any witness to

```text
B < choose(z,t) * |F|^(k-t)
```

under those simple inequalities refutes the raw field-power coordinate-fiber fit.

Follow-up module `LineListAppearanceFiber.lean` now formalizes the replacement object:

```lean
appearingCoordinateAgreementFiber
exactAppearingZeroAgreementFiber
zeroAgreementStratum_subset_appearingCoordinateAgreementFiber_biUnion
zeroAgreementStratum_card_le_choose_mul_appearingCoordinateFiberBound
zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers
zeroAgreementStratum_card_le_choose_mul_exactAppearingZeroAgreementFiberBound
not_zeroAppearingCoordinateFiberBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_iff_exists_sum_gt
zeroAppearingCoordinateFiberBudgetFits_term_le
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_of_exists_term_gt
puncturedZeroStratifiedLineBudgeted_of_appearingCoordinateFiberBudgeted
puncturedZeroStratifiedLineBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformExactAppearingZeroAgreementFiberBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers
exists_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
exactAppearingZeroAgreementFiber_card_le_one_of_k_le
exists_low_exactAppearingFiber_gt_of_exists_fiber_gt_and_high_one
unsafe_or_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
exactAppearingZeroAgreementFiber_card_le_field_pow_sub_card
exactAppearanceFiberSingleton_weighted_le_field_pow_mul_support_div
singletonBadScalarIncidencesInExact_card_le_field_pow_mul_support_div
zeroExactAppearanceFiberSingletonBudgeted_of_rawFieldPowBudget
zeroExactSingletonDefectProfileBudgeted_of_rawFieldPowBudget
uniformLineBadScalarsBudgeted_of_rawFieldPowSingletonBudget
uniformLineBadScalarsBudgeted_of_lowRawFieldPow_highSupportSingletonBudget
exists_largeZero_safe_rawFieldPowSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_rawFieldPowSingletonBudgetFailure_of_not_budgeted
exists_lowRaw_or_highSupportFailure_of_not_budgeted
unsafe_or_lowRaw_or_highSupportFailure_of_not_budgeted
unsafe_or_largeZero_safe_low_exactSingletonProfile_rawFieldPowBarrier_gt_of_not_budgeted
unsafe_or_largeZero_safe_low_exactAppearanceFiberSingleton_rawFieldPowBarrier_gt_of_not_budgeted
```

`LineListSupportRatioFiber.lean` now makes the next replacement object explicit:

```lean
supportRatioFiber
exists_supportRatioFiber_card_ge_sub_of_mem_lineAppearingCodewords
exists_supportRatioFiber_card_ge_sub_of_mem_exactAppearingZeroAgreementFiber
supportRatioHeavyCoordinateFiber
exactAppearingZeroAgreementFiber_subset_supportRatioHeavyCoordinateFiber
supportRatioLineFiberCover
supportRatioHeavyCoordinateFiber_subset_supportRatioLineFiberCover
supportRatioHeavyCoordinateFiber_card_le_supportRatioLineFiberCover_card
supportRatioLineFiberCover_subset_supportRatioHeavyCoordinateFiber
supportRatioLineFiberCover_eq_supportRatioHeavyCoordinateFiber
supportRatioLineFiberCover_card_eq_supportRatioHeavyCoordinateFiber_card
supportRatioLineFiberCover_card_le_sum_coordinateAgreementFibers
supportRatioCoverSum_le_field_card_mul_choose
supportRatioCoverSum_le_field_card_mul_choose_of_k_le_card
supportRatioLineFiberCover_card_le_field_card_mul_choose
supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose
supportRatioHeavyCoordinateFiber_card_le_field_card_mul_choose_n
zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose
zeroSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
ZeroSupportRatioCoverSumBudgeted
zeroSupportRatioHeavyBudgeted_of_coverSumBudgeted
UniformLargeZeroSafeSupportRatioCoverSumBudgeted
zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose
zeroSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
uniformLargeZeroSafeSupportRatioCoverSumBudgeted_of_lineFiberCoverChoose_n
not_zeroSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
not_uniformLargeZeroSafeSupportRatioCoverSumBudgeted_iff_exists_coverSum_gt
uniformSupportRatioHeavyBudgeted_of_coverSumBudgeted
zeroExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
uniformExactAppearingZeroAgreementFiberBudgeted_of_supportRatioHeavyCoordinateFiberBudgeted
uniformLargeZeroSafeSupportRatioHeavyCoordinateFiberBudgeted_of_lineFiberCoverChoose_n
uniformExactAppearingZeroAgreementFiberBudgeted_of_lineFiberCoverChoose_n
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_lineFiberCoverChoose_n
not_lineFiberCoverChooseBudgetFits_of_not_uniformLineBadScalarsBudgeted
lineFiberCoverChooseBudgetFits_term_le
not_lineFiberCoverChooseBudgetFits_of_exists_term_gt
exists_lineFiberCoverChooseBudgetSum_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_supportRatioCoverSums
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coverSum_lineFiberCoverChoose_n
exists_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
exists_low_supportRatioCoverSum_gt_of_exists_coverSum_gt_and_high_choose
unsafe_or_largeZero_safe_low_supportRatioCoverSum_gt_of_not_uniformLineBadScalarsBudgeted
exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
unsafe_or_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
```

For an appearing codeword, the moving-support ratios
`(c i - u0 i) / u1 i` must have a fiber of size at least `a - t`, where `t` is the exact
zero-direction agreement count.  Hence an exact appearance fiber over `S` is contained in the raw
coordinate fiber over `S` plus the extra condition that one support-ratio fiber has size
`a - #S`.  The explicit cover `supportRatioLineFiberCover` then chooses a heavy scalar `γ` and an
`(a - #S)`-element moving-support subfiber `T`, reducing membership to an ordinary coordinate
agreement fiber over `S ∪ T` for the line word `u0 + γ*u1`.  On zero profiles this cover is exact,
not merely one-sided.  If `k <= a`, RS uniqueness bounds every `(γ, T)` coordinate fiber by one,
giving the per-profile envelope
`|F| * choose(#directionSupportSet(u1), a - #S)`.  This is still not a closed prize bound, but it is
the first target that actually uses appearance on the affine line before paying the raw field-power
count.  The ambient-length corollary replaces `#directionSupportSet(u1)` by `n` when a coarser
line-independent expression is useful.  The same file also packages the finite `(γ, T)` sum itself
as a production route: uniform cover-sum budgets imply support-ratio-heavy budgets,
exact-appearance budgets, and a full failure scanner returning an overfull cover sum.  The
scalar-times-binomial bound is now stated directly on that finite cover sum, with an ambient
uniform wrapper, so the cover-sum route has a named control case before any improvement is
attempted.  Failed production under the ambient-binomial cover route now returns a concrete
over-budget weighted `∑_t` expression, and a single over-budget profile term refutes the fit.  The
cover-sum budget itself also has exact failure forms, so future attacks on overlap can start from
an explicit large-zero safe line, zero profile `S`, and overfull finite `(γ, T)` sum without
carrying the full production wrapper.
The cover-sum scanner now has the same low-profile refinement as the heavy-fiber route: if the
candidate envelope dominates
`|F| * choose(#directionSupportSet(u1), a - t)` on every high profile `k <= t < a`, then any
overfull finite cover sum must occur at `t < k`.

`LineListSupportRatioArithmeticObstruction.lean` builds on those fit-term lemmas and records the
parameter-only zero-count obstruction for the ambient support-ratio envelope:

```lean
lineFiberCoverChooseBudgetFits_choose_le_of_support_ge_sub
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_exists_choose_gt
not_lineFiberCoverChooseFit_of_zeroCount_choose_gt
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_two_mul_le
```

The fit with `M(t) = |F| * choose(n, a - t)` contains every individual weighted profile summand.
If a possible direction has `z` zero coordinates and enough remaining moving support to activate
profile `t`, the fit forces `choose(z, t) * |F| * choose(n, a - t) <= B`.  The `z = a`, `t = 0`
instance recovers the `|F| * choose(n, a) <= B` obstruction in the common `2a <= n` range.
Therefore this ambient line-cover envelope can only close targets above its scalar-times-binomial
control surface; below that threshold, the arithmetic fit itself is refuted before any δ*
conclusion.

`LineListSingletonArithmeticObstruction.lean` records the corresponding raw singleton arithmetic
no-go:

```lean
rawFieldPowSingletonProfileBudget_term_le
not_uniformWeightPlusExactSingletonProfileBudgeted_of_rawFieldPow_term_gt
exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le
not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
fieldPow_le_two_mul_of_lowRawSingletonBudget
not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le
unsafe_or_not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
```

The combined `puncturedWeight + profile <= 2B` budget contains each raw weighted singleton summand.
If `D` dominates `|F|^(k-t) * support/(a-t)` on the large-zero branch, any summand above `2B`
refutes the combined budget.  In the common `2a <= n`, `t = 0` case, this gives no fit whenever
`2B < |F|^k` under zero-direction safety; without assuming zero-safety first, the wrapper exposes
the standard zero-direction saturation branch or combined-budget failure.  Thus the raw exact
singleton route is a control/no-go baseline, not a floor proof.  The split low-raw/high-support
variant has the same low-end obstruction when `0 < k`: the `t = 0` profile is already low and
forces `|F|^k <= 2B` if the combined profile budget holds.
The same arithmetic now explicitly covers the split low-raw/high-support certificate: for `0 < k`,
the low raw assumption at `t = 0` and the combined singleton-profile budget imply
`|F|^k <= 2B`, so high-profile support-only savings cannot repair a raw low-profile envelope.

These theorems prove that the same punctured-budget reduction works with
`coordinateAgreementFiber(S) ∩ lineAppearingCodewords`, a subset of the raw affine fiber.  The
numerical saving is still open; the point is that future positive estimates can now target the
right finite set without redoing the line-list plumbing.  The exact-fiber production wrapper also
has the matching scanner: with high exact fibers bounded by uniqueness, any failed uniform budget
must return either zero-direction saturation or an overfull low exact appearance fiber.
The singleton-defect layer also exposes the raw field-power obstruction directly: any remaining
low-profile failure after the high range is discharged can be converted into
`D t < |F|^(k-t) * support/(a-t)`.  Conversely, if that weighted field-power envelope is already
below `D t` for every exact profile, the raw-envelope consumer feeds the exact singleton-profile
production wrapper directly; the split consumer lets callers provide the low raw interpolation
bound and the high support-only bound separately.  The direct converse scanner records the same
field-power obstruction without first passing through a profile-cardinality witness.
The split converse refines that obstruction into low raw interpolation failure versus high
support-denominator failure, plus the standard zero-direction saturation branch.

## Critique of the Previous Hope

The previous optimistic reading was:

1. Cover exact zero-agreement strata by coordinate fibers.
2. Bound each coordinate fiber by the affine interpolation dimension `|F|^(k-t)`.
3. Sum over subsets and hope the production budget absorbs the binomial/support weights.

Step 2 is now proven, but that is precisely why the route can be criticized cleanly.  The proof
does not use that a codeword appears somewhere on the affine line; it counts every polynomial
consistent with the fixed zero-coordinate subset.  At `t = 0`, this already counts the entire RS
message space.  For larger `t`, it still counts all completions of the prescribed values without
asking whether those completions can become heavy for any scalar on the moving support.

The new obstruction records this loss quantitatively.  The field-power route must satisfy every
individual term, not just the full sum.  Since directions with prescribed zero/support counts exist
for free, the arithmetic barrier is not an artifact of a rare direction.  It is a structural
failure of the unconstrained envelope.

## What a Real Replacement Must Use

The next positive theorem cannot be another dimension count for arbitrary fibers.  It must count
appearing codewords:

```text
c in coordinateAgreementFiber(S)
and exists gamma with #agree(c, u0 + gamma*u1) >= a.
```

The missing saving has to come from the moving support.  A plausible replacement envelope should
depend on at least one of:

- the number of support coordinates on which the line word can be matched by one scalar;
- the distribution of ratios `(c i - u0 i) / u1 i` on support coordinates;
- incompatibility between many fixed zero-coordinate values and a large support fiber for one
  scalar;
- a profile/appearance theorem showing that only a small subset of the affine interpolation fiber
  can actually enter `lineAppearingCodewords`.

In other words, the next object should not be

```text
#coordinateAgreementFiber(S).
```

It should be an appearance-filtered fiber such as:

```text
#{c in coordinateAgreementFiber(S) :
    exists gamma, a <= #agree(c, u0 + gamma*u1)}
```

or a stronger ratio-profile partition of that set.  The code already has the per-codeword
heavy-scalar denominator; the remaining saving must happen before summing over the whole affine
fiber.

`LineListSupportRatioFiber.lean` formalizes exactly that stronger partition target.  The next
positive estimate should improve the explicit `(γ, T)` cover sum for codewords in a coordinate
fiber whose support-ratio map has a heavy fiber, rather than all codewords in the coordinate fiber.

## Consequence

This is not a floor proof.  It is a no-go theorem for one tempting route.  The raw field-power
coordinate-fiber envelope is now formally refutable from parameter inequalities alone:

```text
z <= n,
a <= z,
t < a,
a - t <= n - z,
B < choose(z,t) * |F|^(k-t).
```

The `2a <= n` / `t = 0` corollary is the bluntest instance: if `B < |F|^k`, the naive envelope is
already dead.  The more general `z,t` theorem gives scanners a sharper diagnostic: when the raw
field-power sum fails, report the first obstructing binomial term and force the next essay/proof to
explain why those interpolants do not appear on the affine line.
