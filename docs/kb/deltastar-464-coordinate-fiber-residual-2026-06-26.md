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
zeroAgreementStratum_subset_coordinateAgreementFiber_biUnion
zeroAgreementStratum_card_le_sum_coordinateAgreementFibers
zeroAgreementStratum_card_le_choose_mul_coordinateAgreementFiberBound
zeroAgreementStrataCardBudgeted_of_coordinateAgreementFiberBudgeted
puncturedZeroStratifiedLineBudgeted_of_coordinateAgreementFiberBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformCoordinateAgreementFiberBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_coordinateAgreementFibers
exists_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
unsafe_or_largeZero_safe_coordinateAgreementFiber_gt_of_not_uniformLineBadScalarsBudgeted
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

## Critical Assessment

The obvious expected envelope is `M(t) = |F|^(k-t)` for `t <= k`, with the endpoint collapsing to
`1` once `t >= k`.  This is the affine-fiber count for prescribing `t` independent evaluations of
a degree-`< k` polynomial.  The repository already has nearby MDS interpolation infrastructure in
`RSVanishingDim.lean` and `RSWeightEnumerator.lean`, but the current line-list code uses the local
`rsCode` carrier and an arbitrary offset word `u0`; the next proof needs a clean bridge from this
finite set to an affine translate of the vanishing kernel.

This route can still fail to close the floor.  Even if the fiber count is exactly `|F|^(k-t)`, the
binomial factor `choose(#zeroSet(u1), t)` and the weight `support(u1)/(a-t)` may exceed the target
budget for the hard parameters.  That would be an arithmetic failure, not a Lean-interface failure.
The new API is useful because it separates the two questions: prove the fiber count, then check the
weighted binomial fit, or obtain a concrete overfull fiber.

## Next Target

Prove a local affine-fiber theorem:

```text
#coordinateAgreementFiber(dom,k,u0,S) <= |F|^(k - #S)
```

at least when `#S <= k`, using injectivity of `dom` and the existing vanishing-kernel cardinality
lemmas.  Then test whether the induced binomial weighted sum fits the #464 bad-scalar budget on the
large-zero safe branch.
