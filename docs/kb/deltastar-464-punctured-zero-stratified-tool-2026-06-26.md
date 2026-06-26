# Issue #464: punctured zero-stratified line-list tool

Date: 2026-06-26.

Status: one proposed tool survived formalization.  It is not a delta-star proof.

## Critique of the last essay

The previous large-zero trichotomy essay correctly isolated the residual:

```text
#zero(u1) >= a,
ZeroDirectionSafeLine dom k a u0 u1,
but lineBadScalars is still over budget.
```

But it left the residual too coarse.  It treated the large-zero safe branch as a separate theorem,
which is honest but not yet mathematical.  The missing observation is that zero-direction safety is
not just a Boolean guard.  It supplies, for every codeword, a positive denominator:

```text
a - #directionZeroAgreementSet(c,u0,u1).
```

The full zero set may be huge, but a fixed codeword only gets free scalar-independent agreements on
the zero coordinates where it actually equals the offset.  That is the right puncturing parameter.

## The tool that held up

`CodewordHeavyScalar.lean` now proves:

```lean
agreeSet_line_card_le_zeroAgreement_add_movingFiber
codeword_heavy_scalar_card_le_support_div_sub_zeroAgreement
```

The second theorem says a fixed codeword contributes at most:

```text
support(u1) / (a - #zeroAgreement(c,u0,u1))
```

heavy scalars, provided `#zeroAgreement(c,u0,u1) < a`.  This is exactly the zero-direction safety
hypothesis for codewords in the RS code.

`LineListReduction.lean` lifts this to the line:

```lean
zeroAgreementStratum
puncturedZeroStratifiedLineWeight
PuncturedZeroStratifiedLineBudgeted
UniformPuncturedZeroStratifiedLineBudgeted
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
```

The key bound is:

```text
#lineBadScalars <=
  sum_{c appearing on the line}
    support(u1) / (a - #zeroAgreement(c,u0,u1)).
```

This is a real improvement over the blunt support-eligible denominator
`support(u1)/(a - #zeroSet(u1))`.  It remains useful when `#zeroSet(u1) >= a`.

The regrouping theorem also survived formalization:

```lean
puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
```

Under zero-direction safety, the codeword-weighted sum is exactly:

```text
sum_{t=0}^{a-1}
  #zeroAgreementStratum(t) * support(u1)/(a-t).
```

So the word "stratified" is not only descriptive.  The Lean object can be attacked either as a
weighted appearing-codeword list or as a family of exact `t`-strata.

## What is still missing

The new residual is:

```lean
UniformPuncturedZeroStratifiedLineBudgeted dom k a B
```

with exact failure form:

```lean
not_uniformPuncturedZeroStratifiedLineBudgeted_iff_exists_largeZero_safe_weight_gt
puncturedZeroStratifiedLineWeight_gt_of_lineBadScalars_card_gt
not_uniformPuncturedZeroStratifiedLineBudgeted_of_not_largeZeroSafeLineBadScalarsBudgeted
```

So the next proof or counterexample has a concrete target: find or rule out a large-zero safe line
whose punctured weight exceeds the production budget.  The last bridge says any failed
`LargeZeroSafeLineBadScalarsBudgeted` instance already refutes this stronger punctured-weight
budget.

The promising mathematical direction is a stratum bound.  Let:

```text
t(c) = #directionZeroAgreementSet(c,u0,u1).
```

Then the punctured weight is exactly:

```text
sum_{t=0}^{a-1}
  N_t(u0,u1) * support(u1)/(a-t),
```

where `N_t` is the number of appearing codewords with exactly `t` zero agreements.  This suggests a
new theorem:

```text
ZeroAgreementStratumListBound:
  N_t is small when t is near a,
  because many zero agreements already impose a high-codimension RS restriction.
```

If this theorem is true, it is a genuine coding-theoretic route around the blunt Paley/BGK route for
this branch.  If it is false, the counterexample should be highly structured: many RS codewords
nearly agree with `u0` on the zero set, none reaches `a`, and their moving-support fibers still
cover too many scalars.

## Refutation pressure

The tool can fail in two ways:

1. The punctured weight can still be as large as field size for adversarial `u0,u1`, even under
   zero-direction safety.  Then the line-list route collapses back to global incidence.
2. The weight may be small for natural monomial directions but large for arbitrary `WordStack`
   directions.  Then the same global-max problem reappears under a different name.

The scanner obligation is now clear:

```text
not support eligible,
zero-direction safe,
puncturedZeroStratifiedLineWeight > B.
```

This is the next target to probe or prove.  The prize is still open, but the large-zero branch is no
longer an undefined exception; it has a computable summation certificate.
