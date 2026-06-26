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
zeroAgreementStratum_subset_appearingCoordinateAgreementFiber_biUnion
zeroAgreementStratum_card_le_choose_mul_appearingCoordinateFiberBound
puncturedZeroStratifiedLineBudgeted_of_appearingCoordinateFiberBudgeted
uniformPuncturedZeroStratifiedLineBudgeted_of_uniformAppearingCoordinateFiberBudgeted
```

These theorems prove that the same punctured-budget reduction works with
`coordinateAgreementFiber(S) ∩ lineAppearingCodewords`, a subset of the raw affine fiber.  The
numerical saving is still open; the point is that future positive estimates can now target the
right finite set without redoing the line-list plumbing.

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
