# DeltaStar #464: coordinate-fiber residual

## Problem

The punctured zero-stratified line-list route reduced the large-zero safe branch to a stratum
envelope:

```text
#zeroAgreementStratum(t) <= N(t)
sum_{t<a} N(t) * support(u1)/(a-t) <= B.
```

This is useful, but it still hides the real RS object.  A `t`-stratum consists of appearing
codewords whose zero-direction agreement set has size exactly `t`.  To prove or refute a candidate
`N(t)`, we need to know how many RS codewords can agree with the offset on a fixed subset of zero
coordinates.

## New Lean Surface

`LineListReduction.lean` now exposes that lower layer:

```lean
coordinateAgreementFiber
ZeroCoordinateAgreementFiberBudgeted
ZeroCoordinateAgreementFiberBudgetFits
coordinateAgreementFiber_card_le_one_of_k_le
coordinateAgreementFiber_card_le_field_pow_sub_card
zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card
uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card
zeroAgreementStratum_card_le_choose_of_k_le_t
zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion
zeroAgreementStratum_card_le_sum_coordinateAgreementFibers
zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
zeroAgreementStrataCardBudgeted_of_coordinateAgreementFiberBudgeted
zeroAgreementStrataCardBudgeted_of_lowStrata_and_highChoose
puncturedZeroStratifiedLineBudgeted_of_coordinateAgreementFiberBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
not_zeroCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_iff_exists_fiber_gt
not_zeroCoordinateAgreementFiberBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_iff_exists_sum_gt
zeroCoordinateAgreementFiberBudgetFits_term_le
fieldPowCoordinateAgreementFiberBudgetFits_term_le
uniformFieldPowCoordinateAgreementFiberBudgetFits_term_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_term_gt
fieldPowCoordinateAgreementFiberBudgetFits_choosePow_le_of_support_ge_sub
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_choosePow_gt
zeroCoordinateAgreementFiberBudgetFits_zeroTerm_le
fieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_zeroTerm_gt
fieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_support_ge
uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
exists_direction_zero_card_eq_support_card_eq
not_fieldPowFiberFit_of_zeroCount_choosePow_gt
exists_largeZero_direction_support_ge_of_two_mul_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le
exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformPunctured
not_zeroAgreementStrataCardBudgeted_iff_exists_low_stratum_gt_of_high_choose
unsafe_or_largeZero_safe_low_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers
exists_low_coordinateAgreementFiber_gt_of_exists_fiber_gt_and_high_one
exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_low_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
```

For a fixed coordinate subset `S`, `coordinateAgreementFiber dom k u0 S` is the finite set of
degree-`< k` RS codewords agreeing with `u0` on every coordinate of `S`.  The stratum cover sends an
appearing codeword to its exact zero-agreement set, so the `t`-stratum is covered by all coordinate
fibers indexed by `t`-subsets of `directionZeroSet(u1)`.

The endpoint theorem is already proved:

```text
#S >= k  ->  #coordinateAgreementFiber(S) <= 1.
```

This is the polynomial uniqueness fact in fiber form: two degree-`< k` codewords agreeing with
`u0` on at least `k` injected domain points must agree with each other on at least `k` points, hence
they are equal.

The endpoint now lifts to the exact zero-agreement stratum:

```text
k <= t  ->  #zeroAgreementStratum(t) <= choose(#directionZeroSet(u1), t).
```

Consequently, if the proposed `N(t)` envelope already dominates that binomial ceiling for every
`k <= t < a`, any remaining stratum-cardinality counterexample must have `t < k`.  The
production scanner has the same refinement: with support-line-list control, support arithmetic, and
large-zero stratum arithmetic fixed, a failed uniform bad-scalar budget reports either
zero-direction saturation or a large-zero safe low stratum `t < k`.

The affine interpolation count is also now proved directly:

```text
#coordinateAgreementFiber(dom,k,u0,S) <= |F|^(k - #S).
```

This is independent of whether the prescribed offset word `u0` is itself a codeword.  If the fiber
is nonempty, choose one polynomial in the fiber; translation by that polynomial injects the fiber
into the kernel of evaluation on `S`, whose cardinality is the existing RS vanishing-kernel count.
The source audit is axiom-clean modulo the standard Lean axioms already used by that substrate:
`propext`, `Classical.choice`, and `Quot.sound`.
The file also packages this as the uniform large-zero-safe coordinate-fiber budget
`M(t) = |F|^(k-t)` and as a production wrapper: if this weighted field-power envelope fits the
large-zero arithmetic, then the coordinate-fiber branch is discharged.

## What It Buys

The route replaces an opaque stratum bound with a finite-field interpolation budget.  If a proposed
fiber envelope `M(t)` satisfies:

```text
#coordinateAgreementFiber(S) <= M(t)
for every S subset directionZeroSet(u1), #S = t,
```

and

```text
sum_{t<a} choose(#directionZeroSet(u1), t) * M(t) * support(u1)/(a-t) <= B,
```

then the punctured large-zero budget follows.  With the support-eligible line-list route,
support-fit arithmetic, and zero-direction safety also fixed, this gives
`UniformLineBadScalarsBudgeted`.

The scanner side is sharper too.  Under the same arithmetic assumptions, a failed uniform
bad-scalar budget now has to return either a zero-direction saturation witness or:

```text
large-zero safe u0,u1,
t < a,
S subset directionZeroSet(u1), #S = t,
M(t) < #coordinateAgreementFiber(S).
```

So a counterexample is no longer just "too many bad scalars" or even "too many codewords in a
stratum"; it is a specific interpolation fiber whose cardinality beats the proposed envelope.
If the proposed envelope is at least one in every high range `k <= t < a`, the scanner can further
force this witness into the low range `t < k`.

## Critical Assessment

The obvious envelope `M(t) = |F|^(k-t)` is now available as
`coordinateAgreementFiber_card_le_field_pow_sub_card`, while the high endpoint `t >= k` is closed
at the sharper singleton/binomial level.  The raw interpolation obstruction is gone with a
standard-axiom proof; any remaining failure of the coordinate-fiber route is either an arithmetic
failure of the weighted binomial sum or a need for a stronger, support-aware low-range estimate.
Under the support-line-list and support-fit hypotheses plus that weighted field-power coordinate
fit, `unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers` says a failed
uniform bad-scalar budget must be zero-direction saturation.
The same arithmetic layer now exposes its first obstruction: the `t = 0` term alone forces
`|F|^k * support(u1) / a <= B`.  Thus the raw field-power route can be refuted before any
higher-stratum information is considered if a large-zero direction violates that zero-term bound.
More generally, every individual summand is now available as a necessary condition; if a direction
and stratum have support at least `a - t`, the fit already forces
`choose(#zeroSet(u1), t) * |F|^(k-t) <= B`.
In particular, a large-zero direction with `support(u1) >= a` forces `|F|^k <= B`; if the target
budget is below `|F|^k`, the naive field-power envelope is arithmetically impossible.
This is now parameter-free in the common `2a <= n` regime: choose `a` zero coordinates and set the
direction to `1` elsewhere, giving a large-zero direction whose support is still at least `a`.
Thus `2a <= n` and `B < |F|^k` refute the raw field-power coordinate-fiber arithmetic fit outright.
The follow-up module `LineListArithmeticObstruction.lean` gives the sharper `z,t` obstruction:
for any `z <= n`, there is a direction with exactly `z` zero coordinates and support `n-z`, so
whenever `a <= z`, `t < a`, `a - t <= n - z`, and
`B < choose(z,t) * |F|^(k-t)`, the raw field-power fit is impossible.
`LineListAppearanceFiber.lean` now supplies the corresponding positive API: replace each raw
`coordinateAgreementFiber` by its intersection with `lineAppearingCodewords`, and the stratum cover
plus punctured-budget consumer still go through.  The next hard estimate is therefore a bound on
these appearance-filtered fibers, not on all affine interpolation completions.
The exact-profile version is now available at the same production layer:
`uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_exactAppearingFibers` consumes
exact zero-agreement appearance-fiber budgets directly, and
`unsafe_or_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted` reduces
any failed budget to either zero-direction saturation or a low exact appearance fiber with
`t < k`, after the high range is discharged by Reed--Solomon uniqueness.

The relevant exact declarations are:

```lean
exactAppearingZeroAgreementFiber
zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers
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
fieldPow_le_two_mul_of_lowRawSingletonBudget
not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le
unsafe_or_largeZero_safe_low_exactSingletonProfile_rawFieldPowBarrier_gt_of_not_budgeted
unsafe_or_largeZero_safe_low_exactAppearanceFiberSingleton_rawFieldPowBarrier_gt_of_not_budgeted
```

Follow-up low/high production wrappers are now available for both appearance-fiber sockets:

```lean
ZeroLowAppearingCoordinateFiberBudgeted
UniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted
zeroAppearingCoordinateFiberBudgeted_of_low_and_high_one
uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_low_and_high_one
uniformLineBadScalarsBudgeted_of_lowAppearingCoordinateFibers
ZeroLowExactAppearingZeroAgreementFiberBudgeted
UniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted
appearingCoordinateAgreementFiber_subset_exactAppearingZeroAgreementFiber_superset_biUnion
appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_supersets
appearingCoordinateAgreementFiber_subset_safeExactSuperset_biUnion
appearingCoordinateAgreementFiber_card_le_sum_exactAppearingZeroAgreementFiber_safeSupersets
appearingCoordinateAgreementFiber_card_le_sum_exactAppearingBudget_safeSupersets
powersetCard_superset_card_le_choose_sdiff
sum_safeSupersets_le_sum_choose_sdiff
appearingCoordinateAgreementFiber_card_le_sum_zeroExactAppearingBudget_safeSupersets
appearingCoordinateAgreementFiber_card_le_chooseProfile_exactBudget_safeSupersets
zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_safeSupersetSums
uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_safeSupersetSums
zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums
uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_exactBudgeted_chooseProfileSums
zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingCoordinateFiberBudgeted
uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowAppearingBudgeted
not_zeroLowAppearingCoordinateFiberBudgeted_of_not_zeroLowExactAppearingBudgeted
not_uniformLowAppearingBudgeted_of_not_uniformLowExactAppearingBudgeted
zeroLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyCoordinateFiberBudgeted
uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_of_lowSupportRatioHeavyBudgeted
not_zeroLowSupportRatioHeavyBudgeted_of_not_zeroLowExactAppearingBudgeted
not_uniformLowSupportRatioHeavyBudgeted_of_not_uniformLowExactAppearingBudgeted
zeroExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
uniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted_of_low_and_high_one
uniformLineBadScalarsBudgeted_of_lowExactAppearingFibers
exists_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted
not_zeroLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
not_uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_iff_exists_low_fiber_gt
not_zeroLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
not_uniformLargeZeroSafeLowExactAppearingZeroAgreementFiberBudgeted_iff_exists_low_fiber_gt
exists_low_appearingCoordinateFiber_gt_of_exists_low_exactAppearingFiber_gt
exists_uniformLow_appearingCoordinateFiber_gt_of_exists_uniformLow_exactAppearingFiber_gt
zeroLowAppearingCoordinateFiberBudgeted_of_lowExactBudgeted_mixedChooseProfileSums
uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSums
uniformLargeZeroSafeLowAppearingCoordinateFiberBudgeted_of_lowExact_mixedChooseProfileSumsFit
uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums
uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit
not_uniformLowMixedChooseProfileSumsFit_of_not_uniformLineBadScalarsBudgeted
unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted
exists_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
uniformLargeZeroSafeAppearingCoordinateFiberBudgeted_of_lowExact_fullMixedChooseProfileSums
uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileSums
unsafe_or_largeZero_safe_fullMixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSums
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSumsFit
unsafe_or_not_uniformLowSupportRatioMixedChooseProfileSumsFit_of_not_budgeted
unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfile_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileSums
unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfile_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileCardSums
unsafe_or_largeZero_safe_low_supportRatioMixedChooseProfileCard_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_fullMixedChooseProfileCardSums
unsafe_or_largeZero_safe_fullSupportRatioMixedChooseProfileCard_gt_of_not_budgeted
ZeroLowMixedChooseProfileSumsFit
UniformLargeZeroSafeLowMixedChooseProfileSumsFit
not_zeroLowMixedChooseProfileSumsFit_iff_exists_sum_gt
not_uniformLargeZeroSafeLowMixedChooseProfileSumsFit_iff_exists_sum_gt
lowMixedChooseProfileSumsFit_term_le
lowMixedChooseProfileSumsFit_exact_le
lowMixedChooseProfileSumsFit_high_choose_le
not_zeroLowMixedChooseProfileSumsFit_of_exists_term_gt
not_zeroLowMixedChooseProfileSumsFit_of_high_choose_gt
uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileCardSums
unsafe_or_largeZero_safe_low_mixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileCardSums
unsafe_or_largeZero_safe_fullMixedChooseProfileCard_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_mixedChooseProfileSums
unsafe_or_largeZero_safe_fieldPow_mixedProfile_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_lineFiberCoverFieldPow_fullMixedChooseProfileSums
unsafe_or_largeZero_safe_fieldPow_fullMixedProfile_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardSums
unsafe_or_largeZero_safe_fieldPow_mixedProfileCard_gt_of_not_budgeted
uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardSums
unsafe_or_largeZero_safe_fieldPow_fullMixedProfileCard_gt_of_not_budgeted
fieldPowMixedProfileCardSum
FieldPowMixedProfileCardFit
FieldPowFullMixedProfileCardFit
not_fieldPowMixedProfileCardFit_iff_exists_sum_gt
not_fieldPowFullMixedProfileCardFit_iff_exists_sum_gt
fieldPowMixedProfileCardFit_term_le
fieldPowFullMixedProfileCardFit_term_le
fieldPowMixedProfileCardFit_exact_le
fieldPowMixedProfileCardFit_high_choose_le
not_fieldPowMixedProfileCardFit_of_exact_gt
not_fieldPowMixedProfileCardFit_of_high_choose_gt
fieldPowFullMixedProfileCardFit_exact_le
fieldPowFullMixedProfileCardFit_high_choose_le
not_fieldPowFullMixedProfileCardFit_of_exact_gt
not_fieldPowFullMixedProfileCardFit_of_high_choose_gt
uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardFit
unsafe_or_not_fieldPow_mixedProfileCardFit_of_not_budgeted
uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardFit
unsafe_or_not_fieldPow_fullMixedProfileCardFit_of_not_budgeted
mixedChooseProfileCardSum_le_topCard
uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSums
unsafe_or_largeZero_safe_low_mixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSums
unsafe_or_largeZero_safe_fullMixedChooseProfileTop_gt_of_not_uniformLineBadScalarsBudgeted
fieldPowMixedProfileCardSum_le_topCard
FieldPowMixedProfileTopFit
FieldPowFullMixedProfileTopFit
not_fieldPowMixedProfileTopFit_iff_exists_sum_gt
not_fieldPowFullMixedProfileTopFit_iff_exists_sum_gt
uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileTopFit
unsafe_or_not_fieldPow_mixedProfileTopFit_of_not_budgeted
uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileTopFit
unsafe_or_not_fieldPow_fullMixedProfileTopFit_of_not_budgeted
```

These wrappers let a future positive proof provide only the low-profile estimates `t < k`, while
the high range `k <= t < a` is discharged by Reed--Solomon uniqueness as soon as the envelope
satisfies `1 <= M t` there.

The low exact-appearance socket can also be fed directly from the coarser low appearance-coordinate
socket, because exact zero-agreement appearance fibers are subsets of the corresponding
appearance-coordinate fibers.  Thus one low-profile appearance estimate now serves both the coarse
and exact production routes.  Conversely, if the low exact route fails, then the coarser low
appearance-coordinate route already fails; the exact route has no separate failure mode.
The support-ratio-heavy route sharpens this further: if the low exact route fails, the low
support-ratio-heavy budget already fails too.

The reverse direction is now explicit but lossy.  A coarse appearance-coordinate fiber over
`S ⊆ directionZeroSet u1` is covered by exact zero-agreement fibers over all exact profiles
`T` with `S ⊆ T ⊆ directionZeroSet u1`; cardinally this costs the full sum over those supersets.
Therefore exact-profile estimates recover coarse appearance estimates only after paying this
superset combinatorial factor.
On the zero-safe branch the superset sum can be restricted to exact profiles with `#T < a`, since
an appearing codeword whose exact zero-agreement profile has size at least `a` would violate
`ZeroDirectionSafeLine`.  The new `*_safeSupersets` wrappers package this as a direct consumer:
a full exact-profile budget `Mexact` yields a coarse appearance-coordinate budget `Mcoarse` once
every zero-safe superset sum of `Mexact` is bounded by `Mcoarse`.
The safe superset sum now has a closed cardinality-profile envelope:
`powersetCard_superset_card_le_choose_sdiff` injects `r`-element supersets of `S` inside `Z` into
subsets of `Z \ S`, and `sum_safeSupersets_le_sum_choose_sdiff` bounds the whole safe sum by
`sum_{r<a} choose(#Z - #S, r - #S) * M r`.  Therefore the exact-to-coarse budget transfer can now
be discharged by the numeric profile condition packaged in
`zeroAppearingCoordinateFiberBudgeted_of_exactAppearingBudgeted_and_chooseProfileSums`.
The split module `LineListAppearanceFiberMixedProfile.lean` removes the remaining full-exact
budget assumption from this route: exact supersets with `r < k` are charged to the caller's low
exact budget, while supersets with `k <= r` cost only the RS singleton ceiling.  Consequently the
new production wrapper `uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSums` leaves a
pure arithmetic residual, and the scanner
`unsafe_or_largeZero_safe_low_mixedChooseProfile_gt_of_not_uniformLineBadScalarsBudgeted` returns
either zero-direction saturation or one oversized mixed choose-profile sum.
The companion `*_fullMixedChooseProfileSums` theorems use the same mixed exact-superset charges
but require the profile inequality for every coarse `t < a`, yielding a full appearance-coordinate
budget when that stronger arithmetic input is available.
The mixed arithmetic residual is now named by `ZeroLowMixedChooseProfileSumsFit` and
`UniformLargeZeroSafeLowMixedChooseProfileSumsFit`.  Its failure is exactly an oversized mixed sum,
and every summand is a necessary condition: `Mcoarse t` must dominate the original low exact
envelope `Mexact t` and each high singleton binomial contribution
`choose(#Z - t, r - t)` for `k <= r < a`.  Consequently one high-superset binomial term above
`Mcoarse t` refutes this route before any further geometry is considered.  The cardinal-profile
wrappers remove the dummy subset parameter: because the sum depends only on
`z = #directionZeroSet(u1)`, the remaining check can be stated as a pure inequality for
`a <= z <= n`.
The named-fit route is now wired into production and scanning directly:
`uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileSumsFit` consumes the uniform mixed
fit, while `unsafe_or_not_uniformLowMixedChooseProfileSumsFit_of_not_budgeted` turns failed
bad-scalar production into either zero-direction saturation or negation of that named arithmetic
fit.
The support-ratio field-power budget is now composed directly into this route: the
`lineFiberCoverFieldPow_*MixedChooseProfile*` theorems instantiate `Mexact r` with
`|F| * choose(n, a-r) * |F|^(k-a)`, so downstream callers no longer have to separately pass a low
exact-appearance budget before checking the mixed profile arithmetic.
The concrete field-power cardinal arithmetic is also packaged by
`fieldPowMixedProfileCardSum`, `FieldPowMixedProfileCardFit`, and
`FieldPowFullMixedProfileCardFit`.  The wrappers
`uniformLineBadScalarsBudgeted_of_fieldPow_mixedProfileCardFit` and
`uniformLineBadScalarsBudgeted_of_fieldPow_fullMixedProfileCardFit` consume those named fits, and
their scanners `unsafe_or_not_fieldPow_mixedProfileCardFit_of_not_budgeted` /
`unsafe_or_not_fieldPow_fullMixedProfileCardFit_of_not_budgeted` strip failed production down to
zero-direction saturation or failure of a finite `(z,t)` arithmetic contract.
The field-power card fit also exposes its single-term obstructions: the same-profile field-power
term and every high singleton binomial term must each fit below `Mcoarse t`; the corresponding
`not_fieldPow*CardFit_of_*_gt` lemmas refute the route from either over-budget term alone.
Monotonicity in the zero-set cardinality is now explicit at the generic mixed-profile level:
`mixedChooseProfileCardSum_le_topCard` reduces any card-profile mixed sum with fixed `Mexact` to
the worst case `z = n`.  The `uniformLineBadScalarsBudgeted_of_lowExact_mixedChooseProfileTopSums`
and `uniformLineBadScalarsBudgeted_of_lowExact_fullMixedChooseProfileTopSums` wrappers consume
those top-cardinality inequalities directly, and their scanners return zero-direction saturation
or one oversized top-cardinality `t` profile.
`LineListAppearanceFiberMixedProfileFit.lean` specializes the same top-cardinality contraction to
the concrete field-power envelope through `FieldPowMixedProfileTopFit` and
`FieldPowFullMixedProfileTopFit`, so the fallback field-power route can be checked as a
one-variable `t` inequality at `z = n`.
The sibling `LineListSupportRatioMixedProfile.lean` keeps the abstract support-ratio-heavy version:
low support-ratio-heavy budgets feed the same mixed-profile sockets before choosing any particular
field-power envelope.  Its cardinal-profile variants expose the same pure `a <= z <= n`
arithmetic residual while keeping `Mheavy` abstract, so a future sharper support-ratio-heavy bound
can bypass the ambient field-power envelope without changing the downstream mixed-profile scanner.
It also has named-fit wrappers
`uniformLineBadScalarsBudgeted_of_lowSupportRatioHeavy_mixedChooseProfileSumsFit` and
`unsafe_or_not_uniformLowSupportRatioMixedChooseProfileSumsFit_of_not_budgeted`, so abstract
support-ratio-heavy inputs share the same residual predicate as the low-exact route.

The negated low-budget forms are now exact scanners too: per-line failure exposes a low profile
`t < k`, zero-coordinate subset `S`, and strict overrun `M t < #fiber(S)`; uniform failure
additionally exposes the large-zero safe line carrying that overrun.  This avoids redoing the same
`by_contra` unpacking in downstream probes.
When zero-direction safety is already part of the caller's hypotheses, the direct production
scanners
`exists_largeZero_safe_low_appearingCoordinateFiber_gt_of_not_uniformLineBadScalarsBudgeted` and
`exists_largeZero_safe_low_exactAppearingFiber_gt_of_not_uniformLineBadScalarsBudgeted` remove the
unsafe branch entirely and return the low large-zero safe witness.
The low exact-overrun witnesses also convert directly to the coarser low appearance-coordinate
overrun witnesses, so exact-budget failure can be compared with the original appearance route
without rebuilding the existential payload.

The mixed choose-profile consumer gives a less wasteful exact-to-coarse socket for the remaining low
appearance-coordinate branch.  For exact supersets of size `r < k`, it charges the supplied exact
budget `Mexact r`; for `k <= r < a`, it uses only the Reed--Solomon singleton ceiling.  Thus a
coarse low-profile appearance-coordinate budget can be proved from low exact estimates plus the
explicit mixed binomial sum over safe supersets.  Its production wrapper feeds the same line-list
bad-scalar consumer, and the scanner localizes failed production to zero-direction saturation or one
large-zero safe coarse profile where that mixed choose-profile sum is too small.

This route can still fail to close the floor.  Even if the fiber count is exactly `|F|^(k-t)`, the
binomial factor `choose(#zeroSet(u1), t)` and the weight `support(u1)/(a-t)` may exceed the target
budget for the hard parameters.  That would be an arithmetic failure, not a Lean-interface failure.
The new API is useful because it separates the remaining questions: the raw fiber count is proved,
so a field-power route must now check the weighted binomial fit or replace the raw count with a
stronger support-aware estimate.
The singleton-defect scanners now make this explicit: after the high range is discharged, a failed
low-profile budget can be localized to a profile where `D t` is already smaller than the raw
weighted field-power term.  The converse consumer is also formalized: if that raw weighted
field-power term fits below `D t` profile-wise, the exact singleton-profile route can consume it
directly.  The split consumer separates low raw interpolation from the high support-only term,
matching the scanner shape.
The direct raw-envelope scanner now localizes failed production to a specific large-zero safe
stratum whose weighted field-power term is already above `D t`.
The split scanner separates this into the actual low/high obligations: a low `t < k` raw
field-power overrun or a high `k <= t` support-denominator overrun.
The split raw route is still arithmetically blocked in the common range: at `t = 0`, the low raw
obligation alone forces `|F|^k <= 2B`, so `2B < |F|^k` requires a genuine appearance-filtered
saving rather than only moving high profiles to the support-denominator bound.

## Next Target

Test the induced low-range arithmetic:

```text
sum_{t<a} choose(#zeroSet(u1), t) * |F|^(k-t) * support(u1)/(a-t) <= B
```

on large-zero safe directions, starting with the necessary zero-term inequality
`|F|^k * support(u1) / a <= B` and its support-large corollary `|F|^k <= B`.  If either already
misses the #464 budget, the next real theorem must use extra geometry of appearing codewords or the
support/zero pattern instead of the raw affine-fiber count.
