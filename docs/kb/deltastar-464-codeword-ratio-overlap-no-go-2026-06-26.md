# delta* #464: fixed-codeword ratio overlap is exhausted, but gives a packing cap

## Thesis

The codeword-indexed singleton support-ratio cover is a useful microscope, but the first
"overlap" hope inside it is false in the most literal way.  For one fixed codeword `c`, the
support-ratio fibers

```text
supportRatioFiber(c,u0,u1,gamma)
```

are pairwise disjoint as `gamma` varies.  Every moving coordinate has exactly one ratio
`(c i - u0 i) / u1 i`.  Therefore a proof cannot save the singleton-cap route by claiming that
many singleton scalars for the same `c` share moving coordinates.  They do not.

This is not a failure of the support-ratio cover.  It is a useful correction: the next saving has
to come from Reed-Solomon interpolation structure or from forcing a second witness codeword, not
from coordinate overlap inside a single fixed codeword.

## What was formalized

`LineListCodewordSingletonSupportRatio.lean` now records the exact fixed-codeword partition:

```lean
disjoint_supportRatioFiber_of_ne
pairwiseDisjoint_supportRatioFiber
directionSupportSet_card_eq_sum_supportRatioFiber
sum_supportRatioFiber_card_le_directionSupportSet_card
```

The singleton-specialized consequence is:

```lean
codewordSingletonWitnessScalars_card_mul_sub_zeroAgreement_le_support
codewordSingletonWitnessScalars_card_le_support_div_sub_zeroAgreement_of_ratioPartition
```

In words, if `c` uniquely witnesses many singleton bad scalars, each such scalar consumes at least
`a - #zeroAgreement(c,u0,u1)` moving coordinates, and those consumed ratio fibers are disjoint.
Thus

```text
#singletonScalars(c) * (a - #zeroAgreement(c)) <= support(u1),
```

which is exactly the old support-denominator obstruction in partition form.

The same module also has the raw cover envelope:

```lean
codewordSingletonSupportRatioCover_card_le_singletonWitness_card_mul_choose
codewordSingletonSupportRatioCover_card_le_field_card_mul_choose
exists_largeZero_safe_codewordSupportRatioCoverFieldChoose_gt_of_not_coverBudgeted
```

That envelope is deliberately a baseline.  If a uniform cover cap fails, Lean can now return a
large-zero safe line and one appearing codeword where even the scalar-times-binomial cover is above
the proposed cap.

The sharper packing fact is also formalized:

```lean
codewordSingletonSupportRatioCover_snd_injOn
codewordSingletonSupportRatioCover_image_snd_subset_support_powerset
codewordSingletonSupportRatioCover_card_le_support_choose
codewordSingletonSupportRatioCover_card_le_support_choose_of_zeroSafe
exists_largeZero_safe_codewordSupportChooseRouteFailure_of_not_budgeted
```

When `a - #zeroAgreement(c) > 0`, the selected set `T` is nonempty, so `T` itself determines
`gamma`.  Thus the entire codeword-indexed cover injects into the ambient family of
`(a - #zeroAgreement(c))`-subsets of `support(u1)`.  This removes the extra scalar/field factor
from the cover cap; the route scanner packages failure of that cap as a concrete large-zero safe
line and codeword.  It is still a packing bound on subsets, not the needed scalar cap.

## Critique of the Previous Hope

The previous essay proposed the codeword-indexed cover as the next formal target:

```text
{(gamma,T) : gamma is singleton for c,
             T subset supportRatioFiber(c,u0,u1,gamma),
             #T = a - #zeroAgreement(c)}
```

That was the right object to define, but the phrase "overlap-multiplicity" was too imprecise.
There are two different kinds of overlap:

1. Coordinate overlap among `supportRatioFiber(c,u0,u1,gamma)` as `gamma` varies.
2. Algebraic overlap among the RS interpolation constraints induced by the selected pairs
   `(gamma,T)`.

The first kind is impossible for a fixed `c`.  The ratio map is a function.  Distinct fibers are
disjoint by definition.  Even the selected nonempty subfibers cannot collide as sets across
different scalars, because any coordinate of `T` recovers the ratio.  So any argument that hopes
many singleton scalars for one codeword reuse the same moving coordinates is dead; the best pure
packing cap is the formalized `choose(#support(u1), a - #zeroAgreement(c))`.

The second kind is still alive.  Even when coordinate fibers are disjoint, the selected
constraints can interact algebraically: different line words `u0 + gamma u1`, different subfibers
`T`, and the uniqueness of `c` as witness may force a second RS codeword or force the line into an
exceptional low-dimensional family.  That is not a finite-set overlap theorem; it is an
interpolation-rigidity theorem.

## Revised Target

The next useful theorem should not be stated as "many support-ratio fibers overlap."  A better
shape is:

```text
If one codeword c uniquely witnesses many scalars gamma, then either
  (a) the disjoint-support denominator bound is already the best possible obstruction,
  (b) the selected interpolation constraints force another codeword witness for many gamma, or
  (c) (u0,u1,c) lies in an explicitly classified exceptional pencil.
```

The route needs a saving over

```text
support(u1) / (a - #zeroAgreement(c)).
```

The only way to get that saving is to use uniqueness of the witness.  The current denominator
bound uses only that singleton witnesses are heavy scalars for `c`; it throws away the statement
"no other codeword is heavy at gamma."  The missing theorem must spend that uniqueness condition.

## New Tool Proposal: Singleton Rigidity Graph

Define a graph whose vertices are singleton scalars for `c`.  Connect `gamma` and `gamma'` when
the two selected subfibers force a low-degree RS interpolant to agree with both line words on a
large enough combined coordinate set.  Because the raw support-ratio fibers are disjoint, an edge
is not coordinate overlap; it is interpolation overlap.

A useful Lean-facing residual would be:

```text
SingletonRigidityGraphDense dom k a u0 u1 c R
```

meaning every set of more than `R` singleton scalars contains an interpolation edge that produces
a second witness or an exceptional-pencil certificate.  The production theorem would consume this
as a direct improvement of `UniformLargeZeroSafeCodewordSingletonBudgeted`.

This is stronger and cleaner than asking for a better cover-card bound.  Cover-card bounds count
subsets; the floor needs a scalar cap.  The new support-choose packing cap is useful bookkeeping,
but if `a - #zeroAgreement(c)` is far from `0`, it is still astronomically larger than the
allowed scalar budget.  The graph should attack scalars directly.

## Verdict

The fixed-codeword support-ratio cover remains the right finite object, and its pure coordinate
packing theory is now essentially complete: ratio fibers partition the moving support, and
nonempty selected subfibers inject into support subsets.  The next attack should be an
interpolation-rigidity or second-witness theorem on singleton scalars, not a coordinate-packing
estimate.

This loop did not close the floor.  It tightened the target by proving that one tempting
structural saving is exactly the old denominator bound in disguise, while the cover itself packs
into ambient moving-support subsets.
