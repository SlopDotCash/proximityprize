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
ZeroAgreementStrataCardBudgeted
ZeroAgreementStrataBudgetFits
UniformLargeZeroSafeZeroAgreementStrataCardBudgeted
UniformLargeZeroSafeZeroAgreementStrataBudgetFits
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight
lineBadScalars_card_le_of_puncturedZeroStratifiedLineBudgeted
puncturedZeroStratifiedLineWeight_eq_sum_zeroAgreementStrata
puncturedZeroStratifiedLineWeight_le_of_zeroAgreementStrataCardBudgeted
puncturedZeroStratifiedLineBudgeted_of_zeroAgreementStrataCardBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_uniformPuncturedZeroStratifiedLineBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_puncturedZeroStratified
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_zeroAgreementStrata
not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_zeroAgreementStrataBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
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

The newest consumer takes that literally:

```lean
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformZeroAgreementStrataCardBudgeted
```

It reduces the punctured-weight theorem to two inputs: a cardinality bound `N t` for every
zero-agreement stratum on every large-zero safe line, and the arithmetic fit
`sum_t N t * support/(a-t) <= B`.

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
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
```

So the next proof or counterexample has a concrete target: find or rule out a large-zero safe line
whose punctured weight exceeds the production budget.  The last bridge says any failed
`LargeZeroSafeLineBadScalarsBudgeted` instance already refutes this stronger punctured-weight
budget.  With a proposed `N(t)` envelope whose weighted sum fits under `B`, any punctured-budget
failure refutes the stratum-cardinality budget itself.

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

The Lean socket for this theorem now exists.  `ZeroAgreementStrataCardBudgeted` states
`#zeroAgreementStratum(t) <= N(t)`, while `ZeroAgreementStrataBudgetFits` is the arithmetic check:

```text
sum_{t < a} N(t) * support(u1)/(a-t) <= B.
```

The uniform large-zero versions imply `UniformPuncturedZeroStratifiedLineBudgeted`.

The scanner side is now equally explicit:

```lean
not_zeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_iff_exists_stratum_gt
not_zeroAgreementStrataBudgetFits_iff_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataBudgetFits_iff_exists_sum_gt
not_uniformLargeZeroSafeZeroAgreementStrataCardBudgeted_of_not_uniformPunctured
```

So a failed `N(t)` route separates into two concrete defects.  Either some large-zero safe line has
a stratum whose actual cardinality exceeds `N(t)`, or the proposed envelope fits the strata but its
weighted arithmetic sum is already too large for the target budget.  If the arithmetic fit is known
and the punctured theorem still fails, the culprit must be an overfull zero-agreement stratum.

The scanner bridge now starts from the production failure itself.  With the arithmetic fit for
`N(t)` fixed, a failed uniform bad-scalar budget reports either an eligible support-line
overbudget, an unsafe zero-direction witness, or an overfull large-zero safe stratum.  Once the
eligible route and zero-direction safety are separately discharged, the same failure necessarily
exhibits a concrete `t < a` with `N(t) < #zeroAgreementStratum(t)`.

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

The scanner obligation is now two-level.  Raw failure is:

```text
not support eligible,
zero-direction safe,
puncturedZeroStratifiedLineWeight > B.
```

After proposing an `N(t)` envelope, the sharper failure is either:

```text
sum_{t < a} N(t) * support(u1)/(a-t) > B,
```

or a concrete stratum witness:

```text
not support eligible,
zero-direction safe,
t < a,
N(t) < #zeroAgreementStratum(t).
```

This is the next target to probe or prove.  The prize is still open, but the large-zero branch is no
longer an undefined exception; it has a computable summation certificate and a stratum-level
counterexample format.

## Continuation: end-to-end stratum failure socket

The stratum envelope now composes with the full support/large-zero trichotomy:

```lean
exists_eligible_or_unsafe_or_largeZero_stratum_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_zeroAgreementStratum_gt_of_not_uniformLineBadScalarsBudgeted
```

The first theorem says that if the large-zero `N(t)` arithmetic fit is fixed, any failed uniform
bad-scalar budget must report one of three witnesses:

```text
support-eligible line over budget,
zero-direction saturation,
large-zero safe line with an overfull zero-agreement stratum.
```

The second theorem is the sharper production-mode scanner.  Once the support-eligible line-list
theorem, support arithmetic fit, uniform zero-direction safety, and large-zero `N(t)` arithmetic fit
are all assumed, any remaining failure of `UniformLineBadScalarsBudgeted` must be:

```text
not support eligible,
zero-direction safe,
t < a,
N(t) < #zeroAgreementStratum(t).
```

So the line-list branch is now factored down to an actual near-code packing statement.  A successful
next proof must bound these strata.  A successful refutation must produce the concrete overfull
stratum, not just a raw bad-scalar excess.

## Continuation: coordinate-fiber route

The stratum target is no longer opaque.  `LineListReduction.lean` now splits it through a
lower-level coordinate-fiber cover:

```lean
coordinateAgreementFiber
ZeroCoordinateAgreementFiberBudgeted
ZeroCoordinateAgreementFiberBudgetFits
coordinateAgreementFiber_card_le_one_of_k_le
coordinateAgreementFiber_card_le_field_pow_sub_card
zeroCoordinateAgreementFiberBudgeted_field_pow_sub_card
uniformLargeZeroSafeCoordinateAgreementFiberBudgeted_field_pow_sub_card
uniformFieldPowCoordinateAgreementFiberBudgetFits_term_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_term_gt
fieldPowCoordinateAgreementFiberBudgetFits_choosePow_le_of_support_ge_sub
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_choosePow_gt
uniformFieldPowCoordinateAgreementFiberBudgetFits_zeroTerm_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_zeroTerm_gt
uniformFieldPowCoordinateAgreementFiberBudgetFits_cardPow_le_of_exists_support_ge
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_exists_support_ge
exists_direction_zero_card_eq_support_card_eq
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_zero_count_choosePow_gt
exists_largeZero_direction_support_ge_of_two_mul_le
not_uniformLargeZeroSafeCoordinateAgreementFiberBudgetFits_fieldPow_of_two_mul_le
zeroAgreementStratum_card_le_choose_of_k_le_t
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_fieldPowCoordinateFibers
unsafe_of_not_uniformLineBadScalarsBudgeted_with_fieldPowCoordinateFibers
exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_low_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
```

The coordinate-fiber route covers a `t`-stratum by the raw RS fibers indexed by `t`-subsets of
`directionZeroSet(u1)`: how many degree-`< k` codewords can agree with `u0` on a prescribed
zero-subset.  It already proves the rigid endpoint
`coordinateAgreementFiber_card_le_one_of_k_le`: once the prescribed subset has size at least `k`,
there is at most one codeword.  The endpoint now lifts to the stratum-level ceiling
`#zeroAgreementStratum(t) <= choose(#directionZeroSet(u1), t)` for every `k <= t`.

The new production scanner says that, after support-line-list control, support arithmetic,
zero-direction safety, high-binomial stratum domination, and coordinate-fiber arithmetic are fixed,
a failed uniform bad-scalar budget must produce a large-zero safe line and a low stratum `t < k`.
With coordinate-fiber arithmetic fixed, it can be sharpened further to a zero-coordinate subset `S`
of size `t` and `M(t) < #coordinateAgreementFiber(S)`.  The affine RS fiber bound is now proved as
`#coordinateAgreementFiber(S) <= |F|^(k - #S)` with only the standard Lean axioms.  Therefore the
field-power production wrapper leaves only the weighted binomial arithmetic fit; if that fit fails,
the next theorem must exploit extra support/appearance geometry beyond the raw affine fiber count.
Each summand is now exposed as a necessary condition.  Under support at least `a - t`, the `t`
summand alone forces `choose(#zeroSet(u1), t) * |F|^(k-t) <= B`; in particular, `t = 0` forces
`|F|^k * support(u1) / a <= B` on every large-zero direction.  For any such direction with support
at least `a`, this collapses to `|F|^k <= B`.  The source now constructs such a direction from
`2a <= n`, so the naive field-power fit is dead in that parameter range when `B < |F|^k`.
The arithmetic-obstruction module generalizes this witness: for every `z <= n`, there is a
direction with exactly `z` zeros and support `n-z`, so any single term with `a <= z`, `t < a`,
`a - t <= n-z`, and `B < choose(z,t) * |F|^(k-t)` refutes the raw field-power fit.
