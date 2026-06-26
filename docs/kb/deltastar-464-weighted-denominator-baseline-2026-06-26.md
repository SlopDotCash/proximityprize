# delta* #464: weighted denominator is the scalar baseline

## Thesis

The weighted support-choose route is useful cover accounting, but the scalar baseline below it is
the weighted denominator sum:

```text
sum_{c appearing} #support(u1)/(a - #zeroAgreement(c)).
```

This is the codeword-by-codeword version of the old support-denominator obstruction.  It controls
singleton bad-scalar defects directly and is always no larger than the weighted support-choose
sum on zero-safe lines.

## Lean Surface

`LineListCodewordSingletonSupportDivWeight.lean` defines:

```lean
codewordSupportDivWeight
UniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted
```

and proves the direct production route:

```lean
singletonBadScalarDefect_le_codewordSupportDivWeight_of_zeroSafe
lineBadScalars_card_le_of_weight_add_codewordSupportDiv_le_two_mul
largeZeroSafeLineBadScalarsBudgeted_of_codewordSupportDivWeightBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordSupportDivWeightBudget
```

It also has the exact failure form:

```lean
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_iff_exists_weight_gt
exists_largeZero_safe_codewordSupportDivWeight_gt_of_not_uniformLineBadScalarsBudgeted
```

Finally, weighted support-choose implies this sharper denominator budget:

```lean
codewordSupportDivWeight_le_codewordSupportChooseWeight_of_zeroSafe
uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_codewordSupportChooseWeightBudget
```

`LineListCodewordSupportDivArithmeticObstruction.lean` adds the one-term arithmetic no-go:

```lean
codewordSupportDivWeight_term_le
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_term_gt
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_profile_term_gt
not_uniformLargeZeroSafeWeightPlusCodewordSupportDivBudgeted_of_exists_support_lower_term_gt
```

This does not claim that every failed denominator sum has one over-budget term.  It records the
useful certificate in the other direction: if one concrete appearing codeword profile already
makes `2B < puncturedWeight + support / (a - zeroAgreement)`, the uniform weighted denominator
budget is impossible.

## Consequence

The next scalar theorem should beat `codewordSupportDivWeight`, not merely the
support-choose census.  A line where

```text
2B < puncturedWeight + codewordSupportDivWeight
```

is now the smaller obstruction returned by the scanner once support-side hypotheses and
zero-direction safety are fixed.  Any genuine progress has to spend singleton uniqueness,
second-witness forcing, or RS interpolation rigidity to improve this denominator sum.

## Verdict

This does not close the floor.  It removes one more accounting ambiguity: coordinate-packing
support-choose bounds are cover control, while weighted denominator is the current scalar
baseline for the singleton-defect route.
