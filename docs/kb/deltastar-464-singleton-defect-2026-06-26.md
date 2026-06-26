# DeltaStar #464: singleton-defect multiplicity fallback

Date: 2026-06-26.

Status: loop progress, not a delta-star proof.

## Thesis

The factor-two multiplicity route does not need the boolean condition "no bad scalar has a unique
witness."  It is enough to count the singleton witness fibers and pay for them as an additive
defect.

The formal inequality is:

```text
2 * #badScalars <= puncturedZeroStratifiedLineWeight + singletonBadScalarDefect.
```

So the production obligation can be weakened to:

```text
puncturedZeroStratifiedLineWeight + singletonBadScalarDefect <= 2 * B.
```

## Lean Surface

`LineListIncidenceMultiplicity.lean` now names the singleton object and its counting forms:

```lean
singletonBadScalars
mem_singletonBadScalars
singletonBadScalars_subset_lineBadScalars
mem_singletonBadScalars_iff_exists_uniqueWitnessCodeword
singletonBadScalarDefect
singletonBadScalarDefect_eq_sum_indicator
singletonBadScalarDefect_le_lineBadScalars_card
singletonBadScalarDefect_eq_zero_iff_noUniqueBadScalarWitness
singletonBadScalarDefect_eq_zero_iff_secondWitnessProperty
singletonBadScalarDefect_pos_iff_not_noUniqueBadScalarWitness
singletonBadScalarDefect_pos_iff_exists_uniqueWitnessCodeword
singletonBadScalars_eq_lineBadScalars_of_uniqueDecoding
singletonBadScalarDefect_eq_lineBadScalars_card_of_uniqueDecoding
codewordSingletonWitnessScalars
mem_codewordSingletonWitnessScalars
codewordSingletonWitnessScalars_subset_lineBadScalars
codewordSingletonWitnessScalars_subset_codewordHeavyScalars
codewordSingletonWitnessScalars_subset_singletonBadScalars
pairwiseDisjoint_codewordSingletonWitnessScalars
biUnion_codewordSingletonWitnessScalars_eq_singletonBadScalars
singletonBadScalarDefect_eq_sum_codewordSingletonWitnessScalars
singletonBadScalarDefect_le_of_codewordSingletonWitnessScalars
singletonBadScalarDefect_le_of_lineListBudgeted_and_codewordSingletonWitnessScalars
```

The incidence inequalities are:

```lean
lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
lineBadScalars_card_le_puncturedWeight_add_singletonDefect_div_two
lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
lineBadScalars_card_le_of_weight_add_codewordSingletonBudget_le_two_mul
lineBadScalars_card_le_of_weight_add_lineListSingletonBudget_le_two_mul
```

The uniform production and scanner forms are:

```lean
UniformLargeZeroSafeSingletonDefectZero
uniformLargeZeroSafeNoUnique_iff_singletonDefectZero
uniformLargeZeroSafeSecondWitness_iff_singletonDefectZero
UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
UniformLargeZeroSafeCodewordSingletonBudgeted
UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted
UniformLargeZeroSafeLineListBudgeted
UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
largeZeroSafeLineBadScalarsBudgeted_of_codewordSingletonBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSingletonBudget
largeZeroSafeLineBadScalarsBudgeted_of_lineListSingletonBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_lineListSingletonBudget
exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_codewordSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_codewordSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_lineListSingletonBudgetFailure_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_lineListSingletonCap_gt_of_not_uniformLineBadScalarsBudgeted
```

`LineListSingletonDefectGeometry.lean` refines the same defect into an incidence graph and exact
zero-agreement profiles:

```lean
singletonBadScalarIncidences
singletonBadScalarIncidences_card_eq_singletonBadScalarDefect
singletonBadScalarDefect_le_lineHeavyIncidences_card
singletonBadScalarDefect_le_puncturedZeroStratifiedLineWeight
singletonBadScalarIncidencesInExactZeroAgreementFiber
disjoint_singletonBadScalarIncidencesInExactZeroAgreementFiber_of_ne
snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div
ZeroExactSingletonDefectProfileBudgeted
ZeroExactSingletonDefectProfileBudgetFits
UniformLargeZeroSafeExactSingletonDefectProfileBudgeted
UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted
ZeroExactAppearanceFiberSingletonBudgeted
UniformLargeZeroSafeExactAppearanceFiberSingletonBudgeted
zeroExactSingletonDefectProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
uniformExactSingletonProfileBudgeted_of_exactAppearanceFiberSingletonBudgeted
zeroExactAppearanceFiberSingletonBudgeted_of_exactAppearingZeroAgreementFiberBudgeted
uniformExactAppearanceFiberSingletonBudgeted_of_exactAppearingFiberBudgeted
singletonBadScalarIncidences_subset_biUnion_exactProfiles
singletonBadScalarIncidencesInExact_subset_singletonBadScalarIncidences
biUnion_exactSingletonProfiles_subset_singletonBadScalarIncidences
singletonBadScalarIncidences_eq_biUnion_exactProfiles
singletonBadScalarIncidences_card_eq_sum_exactSingletonProfiles
singletonBadScalarDefect_eq_sum_exactSingletonProfiles
singletonBadScalarDefect_le_sum_exactSingletonProfiles
singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted_and_fits
uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactSingletonProfileBudget
uniformLargeZeroSafeWeightPlusSingletonDefectBudgeted_of_exactAppearanceFiberSingletonBudget
lineBadScalars_card_le_of_weight_add_exactSingletonProfileBudget_le_two_mul
largeZeroSafeLineBadScalarsBudgeted_of_exactSingletonProfileBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
uniformLineBadScalarsBudgeted_of_exactAppearanceFiberSingletonBudget
uniformLineBadScalarsBudgeted_of_exactAppearingFiberBudget
exists_largeZero_safe_exactSingletonProfileBudgetFailure_of_not_budgeted
exists_largeZero_safe_exactAppearanceFiberSingletonBudgetFailure_of_not_budgeted
exists_largeZero_safe_exactAppearingFiberMultiplier_gt_of_not_budgeted
unsafe_or_largeZero_safe_exactAppearingFiberMultiplier_gt_of_not_budgeted
exists_largeZero_safe_exactSingletonProfile_gt_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_exactAppearanceFiberSingleton_gt_of_not_uniformLineBadScalarsBudgeted
exactAppearingZeroAgreementFiber_card_le_one_of_k_le
exactAppearanceFiberSingleton_weighted_le_support_div_of_k_le
singletonBadScalarIncidencesInExact_card_le_support_div_of_k_le
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
exists_low_exactSingletonProfile_gt_of_exists_profile_gt_and_high_support
exists_low_exactAppearanceFiberSingleton_gt_of_exists_profile_gt_and_high_support
exists_largeZero_safe_low_exactSingletonProfile_gt_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_low_exactAppearanceFiberSingleton_gt_of_not_budgeted
unsafe_or_largeZero_safe_low_exactSingletonProfile_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_low_exactAppearanceFiberSingleton_gt_of_not_budgeted
exists_largeZero_safe_low_exactSingletonProfile_rawFieldPowBarrier_gt_of_not_budgeted
exists_largeZero_safe_low_exactAppearanceFiberSingleton_rawFieldPowBarrier_gt_of_not_budgeted
unsafe_or_largeZero_safe_low_exactSingletonProfile_rawFieldPowBarrier_gt_of_not_budgeted
unsafe_or_largeZero_safe_low_exactAppearanceFiberSingleton_rawFieldPowBarrier_gt_of_not_budgeted
```

`LineListSupportRatioFiber.lean` inserts the missing structural filter between exact appearance
and raw interpolation:

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
exists_low_supportRatioHeavyCoordinateFiber_gt_of_exists_fiber_gt_and_high_one
unsafe_or_largeZero_safe_low_supportRatioHeavyCoordFiber_gt_of_not_uniformLineBadScalarsBudgeted
```

An exact appearance witness over a zero set `S` must have some support-ratio fiber of size at least
`a - #S`.  Thus the exact appearance budget can be proved by counting only coordinate-fiber
codewords with a heavy support-ratio fiber.  The new cover extracts a heavy scalar `γ` and an
`(a - #S)`-subset `T` of its moving support fiber, then covers the codeword by the ordinary
coordinate-agreement fiber for the line word `u0 + γ*u1` on `S ∪ T`.  On zero profiles this cover
is exact, and when `k <= a` RS uniqueness bounds each `(γ, T)` coordinate fiber by one.  This gives
the concrete budget `|F| * choose(#directionSupportSet(u1), a - t)` for the support-ratio-heavy
fiber at zero-profile size `t`, with a coarser ambient variant using `n.choose (a - t)`.  Failed
production localizes, after high profiles are discharged by RS uniqueness, to a low `t < k`
support-ratio-heavy coordinate fiber.  The finite `(γ, T)` cover sum is also exposed as its own
budget interface and scanner, so a future improvement can attack overlap or structure inside the
cover before collapsing to the scalar-times-binomial envelope.  The scalar-times-binomial baseline
is now proved directly for that cover sum, with an ambient uniform wrapper feeding the same
production route.  The ambient-binomial route now has exact arithmetic scanners: failed production
returns an over-budget weighted `∑_t`, a single over-budget weighted profile refutes the fit, and
the separate arithmetic-obstruction module turns zero/support count witnesses into
scalar-times-binomial no-go statements.  The cover-sum budget itself now has exact failure forms,
so the next structural-overlap attack can start from a specific overfull large-zero safe
`(u0,u1,t,S)` cover sum.

`LineListSupportRatioArithmeticObstruction.lean` adds the parameter-only zero-count no-go for the
ambient support-ratio envelope:

```lean
lineFiberCoverChooseBudgetFits_choose_le_of_support_ge_sub
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_exists_choose_gt
not_lineFiberCoverChooseFit_of_zeroCount_choose_gt
not_uniformLargeZeroSafeAppearingCoordinateFiberBudgetFits_lineCoverChoose_of_two_mul_le
```

If a possible large-zero direction has `z` zero coordinates and enough moving support to activate
profile `t`, the ambient-binomial appearance-fiber fit forces
`choose(z, t) * |F| * choose(n, a - t) <= B`.  The `z = a`, `t = 0` instance gives the familiar
`|F| * choose(n, a) <= B` obstruction in the common `2a <= n` range.  Thus the ambient
support-ratio envelope is a control surface, not the final floor estimate; a winning proof still
has to beat that scalar-times-binomial arithmetic.

`LineListSingletonArithmeticObstruction.lean` adds the raw singleton arithmetic no-go:

```lean
rawFieldPowSingletonProfileBudget_term_le
not_uniformWeightPlusExactSingletonProfileBudgeted_of_rawFieldPow_term_gt
exists_rawFieldPowSingletonProfileBudget_term_gt_of_two_mul_le
not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
fieldPow_le_two_mul_of_lowRawSingletonBudget
not_uniformWeightPlusExactSingletonProfileBudgeted_lowRaw_of_two_mul_le
unsafe_or_not_uniformWeightPlusExactSingletonProfileBudgeted_rawFieldPow_of_two_mul_le
```

It proves the combined exact singleton-profile budget contains every raw weighted singleton summand.
If the raw envelope already exceeds `2B` at one summand, the combined budget is impossible; under
`2a <= n`, the `t = 0` direction gives this obstruction from `2B < |F|^k`.  The unsafe-or wrapper
removes the need to assume zero-direction safety before using the obstruction.
The split low-raw/high-support variant does not evade this: when `0 < k`, the low-side hypothesis
at `t = 0` plus the combined profile budget already forces `|F|^k <= 2B`, so the same target
range is impossible even though high profiles use only the support-denominator cap.

This is the bridge from the additive defect to the existing exact appearance-fiber surface.
Bounding singleton defects can now be attempted profile-by-profile over exact zero-direction
agreement sets.

The profile-budget consumer makes this actionable.  A proposed envelope `D t` for singleton-defect
incidences in every exact zero-agreement profile gives:

```text
singletonBadScalarDefect <= sum_{t<a} choose(#zeroSet(u1), t) * D(t).
```

The corresponding production wrapper discharges the large-zero safe branch from the combined
arithmetic:

```text
puncturedZeroStratifiedLineWeight
+ sum_{t<a} choose(#zeroSet(u1), t) * D(t)
<= 2B.
```

The exact-profile split is now an equality on zero-safe lines: the singleton-defect incidence graph
is exactly the biUnion of exact zero-agreement profile slices, and `singletonBadScalarDefect` is the
corresponding double sum.  Thus if every exact profile is below `D t`, the total singleton defect
fits the binomial sum above without union-overlap slack.  The converse scanners localize any failed
uniform bad-scalar budget, after support arithmetic, zero-safety, and the relevant profile envelope
are fixed, either to failed combined profile arithmetic or to a concrete exact profile whose
singleton-defect or exact-appearance weighted size exceeds `D t`.

The exact-appearance bridge is the new attack surface.  It is enough to bound
`exactAppearingZeroAgreementFiber` by profile and multiply by the moving-support denominator
`support/(a-t)`; that yields the singleton-defect profile budget and the older combined
weight-plus-singleton-defect budget.

The direct exact-appearing-fiber production wrapper now exposes that route in one theorem:
given an exact appearance-fiber envelope `M`, denominator arithmetic
`M(t) * support/(a-t) <= D(t)`, and the combined profile budget using `D`, the uniform
bad-scalar budget follows.  The matching scanner says that, with `M` and the combined `D`
arithmetic fixed, any failed uniform bad-scalar budget must produce a large-zero safe line and
profile where `D(t) < M(t) * support/(a-t)`.

The multiplier scanner also has the full failure split: without assuming zero-direction safety
first, the same hypotheses return either a saturating zero-direction codeword or the large-zero
safe multiplier overrun.

The high profile range is now discharged by RS uniqueness plus support arithmetic.  If `k <= t`,
then every exact appearing zero-agreement fiber has size at most one, so both the weighted exact
appearance profile and the exact singleton-defect incidence slice are bounded by
`support/(a-t)`.  Consequently, once the proposed envelope `D t` already dominates that
support-denominator term on all high levels, any overfull exact singleton or exact appearance
profile must occur in the low interpolation range `t < k`.

The low-profile scanners also have full failure split forms.  Without assuming zero-direction
safety in advance, a failed uniform bad-scalar budget now returns either a zero-direction
saturating codeword or a large-zero safe low exact singleton/exact appearance profile.

The raw interpolation barrier is now explicit for this route.  Exact appearance fibers inherit
`#fiber <= |F|^(k-t)`, and both the exact appearance singleton term and the exact singleton-defect
slice are bounded by `|F|^(k-t) * support/(a-t)`.  Therefore a failed production attempt whose high
profiles are already covered can be localized to a low profile where the proposed `D t` sits below
the raw MDS singleton term.  Conversely, if that raw weighted envelope is below `D t` for every
profile and the combined profile arithmetic fits, the raw-envelope production wrapper discharges
the uniform bad-scalar budget.  This does not prove the floor; it says the singleton route must
beat the raw coordinate-fiber envelope in the low interpolation range rather than merely repackage
it.

The sharper positive form is split at `k`: low profiles `t < k` carry the raw MDS term
`|F|^(k-t) * support/(a-t)`, while high profiles `k <= t` only need the support-denominator term.
The theorem `uniformLineBadScalarsBudgeted_of_lowRawFieldPow_highSupportSingletonBudget` packages
exactly that contract.
The direct converse scanner exposes a failed production attempt as either zero-direction
saturation or a large-zero safe profile where the raw weighted field-power term itself exceeds
`D t`.
The split converse makes the residual sharper: after zero-safety, failure is either a low
`t < k` raw MDS overrun or a high `k <= t` support-denominator overrun; without zero-safety there
is the usual saturating-codeword branch.
The standalone raw singleton arithmetic obstruction then shows this raw envelope cannot be the
final floor route in the common `2a <= n`, `2B < |F|^k` range; a positive proof needs an
appearance-filtered or ratio-profile saving.  The low-raw obstruction pins this even for the
split certificate: `t = 0` is already a low profile when `0 < k`, so high-profile support-only
arithmetic cannot rescue a raw low-profile envelope.
The support-ratio-heavy coordinate-fiber interface is the next non-raw target: it asks for a bound
on interpolation completions that also concentrate `a - t` moving-support coordinates at one
scalar.

The per-codeword partition is exact too: singleton bad scalars are the disjoint union of
`codewordSingletonWitnessScalars` over appearing codewords, so the defect can be rewritten as the
sum of those codeword-indexed singleton fibers.  This gives a second attack surface: bound the
number of scalars uniquely witnessed by each codeword, then sum over appearing codewords.
The production wrappers consume either the appearing-codeword count directly or a `LineListBudgeted`
cap, giving bad-scalar bounds from
`puncturedZeroStratifiedLineWeight + #appearing * perCodewordSingletonCap`.
The uniform API is now explicit: `UniformLargeZeroSafeCodewordSingletonBudgeted` supplies the
per-codeword cap, while
`UniformLargeZeroSafeWeightPlusCodewordSingletonBudgeted` uses the actual appearing-codeword count
and `UniformLargeZeroSafeWeightPlusLineListSingletonBudgeted` uses a large-zero-safe line-list cap.
The two scanners localize failed production either to failure of the combined arithmetic or to a
concrete appearing codeword with too many uniquely witnessed singleton scalars.

## Consequence

This changes the next target from an all-or-nothing uniqueness theorem to a quantitative problem:
bound the number of singleton bad scalars on large-zero safe lines.  The old route required every
bad scalar to have a second witness.  The new route permits singleton fibers if their total count
fits inside the remaining factor-two budget.

The scanner is also sharper.  Once support arithmetic and zero-direction safety are fixed, a failed
uniform bad-scalar budget must produce a large-zero safe line where the combined
weight-plus-singleton-defect budget is false.  That failure can be attacked by improving the
punctured-weight term, bounding singleton fibers geometrically, or showing a concrete singleton
profile is impossible.

The endpoints are now exact:

```text
singletonBadScalarDefect = 0
<=> NoUniqueBadScalarWitness
<=> BadScalarSecondWitnessProperty
```

At the other extreme, in the strict Johnson unique-decoding regime every bad scalar has a
singleton witness fiber, so

```text
singletonBadScalarDefect = #badScalars.
```

This proves the defect route is not a hidden improvement in the ordinary unique-decoding zone.  It
is only useful beyond that zone, where singleton fibers can be shown sparse.

## Critique

This does not close #464.  It only decomposes the obstruction.  If singleton witness fibers are as
numerous as the bad scalars themselves, the inequality collapses back to the original union-bound
scale.  The route becomes useful only with a genuine estimate on the singleton defect.

The next nonredundant test is to classify singleton witnesses by exact zero-agreement fiber,
support denominator, or stack-ownership profile and prove that the dangerous profiles are sparse.
