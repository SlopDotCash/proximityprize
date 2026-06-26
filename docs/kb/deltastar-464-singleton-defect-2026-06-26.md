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
largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
```

`LineListSingletonDefectGeometry.lean` refines the same defect into an incidence graph and exact
zero-agreement profiles:

```lean
singletonBadScalarIncidences
singletonBadScalarIncidences_card_eq_singletonBadScalarDefect
singletonBadScalarDefect_le_lineHeavyIncidences_card
singletonBadScalarDefect_le_puncturedZeroStratifiedLineWeight
singletonBadScalarIncidencesInExactZeroAgreementFiber
snd_mem_exactAppearingZeroAgreementFiber_of_mem_singletonBadScalarIncidencesInExact
singletonBadScalarIncidencesInExact_card_le_exactFiber_card_mul_support_div
ZeroExactSingletonDefectProfileBudgeted
ZeroExactSingletonDefectProfileBudgetFits
UniformLargeZeroSafeExactSingletonDefectProfileBudgeted
UniformLargeZeroSafeWeightPlusExactSingletonProfileBudgeted
singletonBadScalarIncidences_subset_biUnion_exactProfiles
singletonBadScalarDefect_le_sum_exactSingletonProfiles
singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted
singletonBadScalarDefect_le_of_exactSingletonProfileBudgeted_and_fits
lineBadScalars_card_le_of_weight_add_exactSingletonProfileBudget_le_two_mul
largeZeroSafeLineBadScalarsBudgeted_of_exactSingletonProfileBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_exactSingletonProfileBudget
exists_largeZero_safe_exactSingletonProfileBudgetFailure_of_not_uniformLineBadScalarsBudgeted
```

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

The converse scanner now localizes any failed uniform bad-scalar budget, after support arithmetic,
zero-safety, and the profile envelope are fixed, to a large-zero safe line whose combined
profile-budget arithmetic is false.

The per-codeword partition is exact too: singleton bad scalars are the disjoint union of
`codewordSingletonWitnessScalars` over appearing codewords, so the defect can be rewritten as the
sum of those codeword-indexed singleton fibers.  This gives a second attack surface: bound the
number of scalars uniquely witnessed by each codeword, then sum over appearing codewords.
The production wrappers consume either the appearing-codeword count directly or a `LineListBudgeted`
cap, giving bad-scalar bounds from
`puncturedZeroStratifiedLineWeight + #appearing * perCodewordSingletonCap`.

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
