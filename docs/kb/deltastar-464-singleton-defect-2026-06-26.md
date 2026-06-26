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
```

The incidence inequalities are:

```lean
lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
lineBadScalars_card_le_puncturedWeight_add_singletonDefect_div_two
lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
```

The uniform production and scanner forms are:

```lean
UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
```

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

## Critique

This does not close #464.  It only decomposes the obstruction.  If singleton witness fibers are as
numerous as the bad scalars themselves, the inequality collapses back to the original union-bound
scale.  The route becomes useful only with a genuine estimate on the singleton defect.

The next nonredundant test is to classify singleton witnesses by exact zero-agreement fiber,
support denominator, or stack-ownership profile and prove that the dangerous profiles are sparse.
