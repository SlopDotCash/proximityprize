# delta* #464: support-choose arithmetic is now an explicit obstruction

## Thesis

The codeword-indexed support-ratio cover now has a clean packing baseline:

```text
cover(c,u0,u1) <= choose(#support(u1), a - #zeroAgreement(c,u0,u1)).
```

That baseline is useful only if the right-hand side fits the production cap `S`.  The new module
`LineListCodewordSupportChooseArithmeticObstruction.lean` makes this necessary condition explicit:
a single large-zero safe line and appearing codeword with

```text
S < choose(support size, a - zero-agreement size)
```

refutes the uniform support-choose budget.

## What was formalized

The direct consumer is:

```lean
codewordSupportChooseBudget_term_le
```

It says any proposed `UniformLargeZeroSafeCodewordSupportChooseBudgeted` must contain the concrete
binomial term attached to every large-zero safe appearing codeword.  The matching no-go forms are:

```lean
not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_choose_gt
not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_profile_choose_gt
not_uniformLargeZeroSafeCodewordSupportChooseBudgeted_of_exists_support_lower_choose_gt
exists_codewordSupportChooseProfile_gt_of_not_uniformLargeZeroSafeBudgeted
```

The last two are the useful working forms.  They replace the raw Lean expression

```text
choose(#support(u1), a - #zeroAgreement(c,u0,u1))
```

by named profile parameters `s` and `z`, and they allow `s` to be only a lower bound on the moving
support size.  Thus a future arithmetic attack can work with profile estimates without unfolding
the finite sets.

The production scanner also has a profile-facing wrapper:

```lean
exists_largeZero_safe_codewordSupportChooseRouteProfileFailure_of_not_budgeted
```

With support-side hypotheses fixed, failed production now returns either the old combined
arithmetic failure or a concrete appearing codeword plus profile data `(s,z)` where
`S < choose(s, a - z)`.

## Consequence

The support-choose baseline is not a hidden source of savings.  It is a necessary binomial
inequality for every large-zero safe appearing codeword.  In any parameter range where a possible
profile has large support and small zero-agreement, the route must pay that binomial term unless a
new RS interpolation, second-witness, or exceptional-pencil theorem beats the pure subset-packing
cap.

This sharpens the next target.  The remaining proof search should either prove that all relevant
large-zero safe profiles make `choose(s, a-z)` small enough, or abandon pure support-choose packing
and attack singleton scalars directly with algebraic rigidity.
