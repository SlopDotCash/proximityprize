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

This route can still fail to close the floor.  Even if the fiber count is exactly `|F|^(k-t)`, the
binomial factor `choose(#zeroSet(u1), t)` and the weight `support(u1)/(a-t)` may exceed the target
budget for the hard parameters.  That would be an arithmetic failure, not a Lean-interface failure.
The new API is useful because it separates the remaining questions: the raw fiber count is proved,
so a field-power route must now check the weighted binomial fit or replace the raw count with a
stronger support-aware estimate.

## Next Target

Test the induced low-range arithmetic:

```text
sum_{t<a} choose(#zeroSet(u1), t) * |F|^(k-t) * support(u1)/(a-t) <= B
```

on large-zero safe directions, starting with the necessary zero-term inequality
`|F|^k * support(u1) / a <= B` and its support-large corollary `|F|^k <= B`.  If either already
misses the #464 budget, the next real theorem must use extra geometry of appearing codewords or the
support/zero pattern instead of the raw affine-fiber count.
