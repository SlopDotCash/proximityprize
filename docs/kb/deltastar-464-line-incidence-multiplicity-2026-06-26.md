# DeltaStar #464: line-list incidence multiplicity

Date: 2026-06-26.

Status: loop progress, not a delta-star proof.

## Thesis

The line-list route was previously phrased as a union bound over appearing codewords:

```text
#badScalars <= sum_c #heavyScalars(c).
```

That is correct, but it hides one possible discount.  If every bad scalar is witnessed by many
codewords, then the incidence graph pays for those multiplicities and the scalar count can be
divided by a witness floor.

## Lean Surface

`LineListIncidenceMultiplicity.lean` now defines the exact bipartite incidence graph:

```lean
badScalarWitnessCodewords
codewordHeavyScalars
lineHeavyIncidences
LineBadScalarMultiplicityFloor
```

The projection identities are explicit:

```lean
lineBadScalars_eq_image_fst_lineHeavyIncidences
lineAppearingCodewords_eq_image_snd_lineHeavyIncidences
```

The incidence cardinality decomposes both ways:

```lean
lineHeavyIncidences_card_eq_sum_badScalarWitnessCodewords
lineHeavyIncidences_card_eq_sum_codewordHeavyScalars
```

The old punctured zero-stratified bound is strengthened to the incidence graph:

```lean
lineHeavyIncidences_card_le_puncturedZeroStratifiedLineWeight
```

and the new conditional discount is:

```lean
not_lineBadScalarMultiplicityFloor_iff_exists_badScalarWitnessCodewords_card_lt
lineBadScalars_mem_of_mem_badScalarWitnessCodewords
badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
lineBadScalarMultiplicityFloor_one
not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
NoUniqueBadScalarWitness
IsUniqueBadScalarWitnessCodeword
badScalarWitnessCodewords_card_eq_one_iff_exists_isUniqueBadScalarWitnessCodeword
BadScalarSecondWitnessProperty
noUniqueBadScalarWitness_iff_secondWitnessProperty
badScalarWitnessCodewords_card_eq_one_of_uniqueDecoding
exists_uniqueWitnessCodeword_of_mem_lineBadScalars_uniqueDecoding
not_noUniqueBadScalarWitness_of_nonempty_uniqueDecoding
not_secondWitnessProperty_of_nonempty_uniqueDecoding
not_lineBadScalarMultiplicityFloor_two_iff_exists_uniqueWitnessCodeword
not_noUniqueBadScalarWitness_iff_exists_uniqueWitnessCodeword
lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
lineBadScalars_card_le_weightDivTwo_of_secondWitness
lineBadScalars_card_le_of_secondWitness_and_weightDivTwo_le
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
lineBadScalars_card_mul_two_le_lineHeavyIncidences_card_add_singletonDefect
lineBadScalars_card_mul_two_le_puncturedWeight_add_singletonDefect
lineBadScalars_card_le_puncturedWeight_add_singletonDefect_div_two
lineBadScalars_card_le_of_weight_add_singletonDefect_le_two_mul
lineBadScalars_card_le_of_weight_add_codewordSingletonBudget_le_two_mul
lineBadScalars_card_le_of_weight_add_lineListSingletonBudget_le_two_mul
not_noUniqueBadScalarWitness_iff_exists_unique_badScalarWitness
exists_unique_badScalarWitness_of_not_lineBadScalars_card_le
exists_uniqueWitnessCodeword_of_not_lineBadScalars_card_le
UniformLargeZeroSafeNoUniqueBadScalarWitness
UniformLargeZeroSafeSecondWitnessProperty
uniformLargeZeroSafeNoUnique_iff_secondWitnessProperty
UniformLargeZeroSafeSingletonDefectZero
uniformLargeZeroSafeNoUnique_iff_singletonDefectZero
uniformLargeZeroSafeSecondWitness_iff_singletonDefectZero
UniformLargeZeroSafePuncturedWeightDivTwoBudgeted
UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_noUnique_and_weightDivTwo
largeZeroSafeLineBadScalarsBudgeted_of_secondWitness_and_weightDivTwo
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_noUniqueWeightDivTwo
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_secondWitnessWeightDivTwo
largeZeroSafeLineBadScalarsBudgeted_of_singletonDefectBudget
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_singletonDefectBudget
exists_largeZero_safe_singletonDefectBudgetFailure_of_not_uniformLineBadScalarsBudgeted
not_uniformLargeZeroSafeSecondWitnessProperty_iff_exists_witness_without_second
exists_largeZero_safe_uniqueWitnessCodeword_of_not_uniformLineBadScalarsBudgeted
exists_largeZero_safe_witness_without_second_of_not_uniformLineBadScalarsBudgeted
lineBadScalars_card_mul_le_puncturedZeroStratifiedLineWeight_of_multiplicityFloor
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_of_multiplicityFloor
lineBadScalars_card_le_of_multiplicityFloor_and_weight_div_le
```

In words:

```text
if every bad scalar has at least R witnessing codewords,
then #badScalars * R <= puncturedZeroStratifiedLineWeight.
```

## What This Changes

This is a third socket next to line-list size and appearance-filtered coordinate fibers.  Instead
of trying to make the appearing-codeword set small, one can try to make its projection to bad
scalars highly many-to-one.

The new residual is not a count of codewords:

```text
for every bad γ, # { codewords c : c is heavy at γ } >= R.
```

If `R > 1`, the budget can be divided by `R`.  If no such multiplicity floor exists, the theorem
collapses to the old union-bound route at `R = 1`.  The negated-floor theorem makes the failure
scanner-facing by producing a bad scalar whose witness-codeword fiber has cardinality `< R`.

The first nontrivial floor is now exact:

```text
R = 1: automatic for every bad scalar.
R = 2 fails iff some bad scalar has exactly one witnessing codeword.
```

So the multiplicity route has a sharp first obstruction: rule out unique-witness bad scalars, or
the route cannot buy even a factor of two.

This first obstruction is named directly as `NoUniqueBadScalarWitness`, with consumers for the
factor-two route:

```text
NoUniqueBadScalarWitness
<=> LineBadScalarMultiplicityFloor ... 2
=> #badScalars <= puncturedZeroStratifiedLineWeight / 2
```

The scanner now exposes the obstruction as data, not only as a cardinal equality:

```text
failed factor-two budget
=> bad scalar gamma + unique witnessing codeword c
```

This is the right shape for the next geometric attack: analyze the single codeword's agreement
set, zero-direction stratum, and appearance fiber directly.

Conversely, the positive proof socket is now explicit:

```text
for every bad scalar gamma and every witness c,
produce a distinct second witness c'
<=> NoUniqueBadScalarWitness
=> factor-two incidence discount
```

This is stronger as a workbench obligation than the negative formulation.  A future proof can try
to manufacture `c'` by symmetry, ownership transfer, or stack geometry; a refutation can exhibit a
single `(gamma, c)` with no second witness.

There is now also a hard fence around that obligation: in the strict unique-decoding regime, any
nonempty witness fiber is forced to be a singleton by the existing Johnson API.  So the
second-witness route cannot be used in half-distance slices where pairwise codeword distance gives

```text
|domain| + (|domain| - d) < 2a.
```

In that regime, any bad scalar directly produces an explicit unique witness codeword and refutes
`NoUniqueBadScalarWitness` / `BadScalarSecondWitnessProperty`.

The route also has a softer fallback that does not require eliminating singleton fibers.  Let
`singletonBadScalarDefect` count bad scalars with exactly one witnessing codeword.  Then:

```text
2 * #badScalars <= puncturedZeroStratifiedLineWeight + singletonBadScalarDefect
```

So a factor-two-style budget can still work if the singleton defect is itself small enough.  This
turns the hard boolean condition "no singleton witnesses" into a quantitative obligation:

```text
punctured weight + singleton defect <= 2B.
```

The matching scanner localizes any failed uniform budget to either a combined
weight-plus-defect arithmetic failure or a concrete witness with no distinct second witness.

The defect endpoints are exact: zero singleton defect is equivalent to the `R = 2` floor /
second-witness property, while strict unique decoding makes the defect maximal
(`singletonBadScalarDefect = #badScalars`).  So the defect fallback is useful only in the
beyond-unique-decoding region where singleton witnesses exist but are sparse.

`LineListSingletonDefectGeometry.lean` then localizes the singleton defect by exact
zero-direction agreement profiles.  It turns the defect into a filtered incidence graph and bounds
each exact-profile slice by the corresponding exact appearance fiber times the usual moving-support
denominator.

That profile split is now an exact partition on zero-safe lines: `singletonBadScalarDefect` equals
the double sum over exact zero-agreement singleton-incidence slices.  If every exact singleton
slice is bounded by `D t`, then the defect is bounded by the corresponding binomial profile sum
without overlap slack.  The bridge `ZeroExactAppearanceFiberSingletonBudgeted` packages the concrete obligation
`#exactAppearingFiber(S) * support/(a-t) <= D t`, and its uniform wrappers feed both the
exact-profile production route and the older weight-plus-singleton-defect route.  The scanners can
now return a specific overfull exact singleton profile, or a specific exact appearance profile
whose support-denominator weighted size exceeds `D t`.

The defect also has a codeword-indexed partition: `codewordSingletonWitnessScalars` are disjoint
over appearing codewords and their cardinals sum exactly to `singletonBadScalarDefect`.  This
separates the remaining problem into per-codeword unique-witness scalar budgets plus an appearing
codeword count.  The production wrappers can use the appearing count directly, or replace it by a
`LineListBudgeted` cap, to prove the final bad-scalar budget from a combined
weight-plus-singleton-cap inequality.

The factor-two branch now also reaches the same production layer used by the support/large-zero
split:

```text
UniformSupportLineListBudgeted
+ SupportAdjustedBudgetFits
+ UniformZeroDirectionSafe
+ UniformLargeZeroSafeNoUniqueBadScalarWitness
+ UniformLargeZeroSafePuncturedWeightDivTwoBudgeted
=> UniformLineBadScalarsBudgeted
```

Equivalently, the large-zero branch can be supplied as
`UniformLargeZeroSafeSecondWitnessProperty`, so the production proof obligation can be stated in
the constructive form rather than the negative no-unique form.

There is also a weaker production branch:

```text
UniformSupportLineListBudgeted
+ SupportAdjustedBudgetFits
+ UniformZeroDirectionSafe
+ UniformLargeZeroSafeWeightPlusSingletonDefectBudgeted
=> UniformLineBadScalarsBudgeted
```

This branch permits singleton witness fibers, but charges their total count against the same
factor-two budget.

This is still conditional.  The substantive new hard input is a uniform proof that large-zero safe
lines have no unique-witness bad scalar, plus the arithmetic proof that the punctured weight divided
by two fits the target budget; or, in the softer branch, a combined bound on punctured weight plus
singleton defect.

The converse scanner is now uniform as well: after the support branch, support arithmetic,
zero-direction safety, and half-weight arithmetic are fixed, failure of
`UniformLineBadScalarsBudgeted` produces a large-zero safe line, a bad scalar, and the unique
witnessing codeword.  This removes the remaining ambiguity about where the factor-two route can
break.

## Companion: Exact Appearance Fibers

`LineListAppearanceFiber.lean` now also splits the appearance-filtered coordinate object by the
actual zero-direction agreement set:

```lean
exactAppearingZeroAgreementFiber
ZeroExactAppearingZeroAgreementFiberBudgeted
UniformLargeZeroSafeExactAppearingZeroAgreementFiberBudgeted
zeroAgreementStratum_card_eq_sum_exactAppearingZeroAgreementFibers
```

The previous `appearingCoordinateAgreementFiber` gives a cover indexed by subsets of the zero
direction.  The exact fiber requires

```text
directionZeroAgreementSet(c,u0,u1) = S
```

so the `t`-stratum is partitioned by the exact `S` rather than merely covered.  This removes one
combinatorial looseness, but it still needs a real bound on the exact fibers to improve the budget.

## Critique

This does not close the floor.  It exposes a possible way around the raw line-list wall, but the
missing theorem is substantial: a lower bound on list multiplicity at every bad scalar is the
opposite direction from ordinary list decoding, which upper-bounds the same fibers.

The most likely failure mode is isolated by the API itself.  A single-witness bad scalar is
equivalent to failure of the first useful multiplicity discount.  A positive use must prove that
the hard large-zero safe lines cannot have such sparse scalar witnesses, probably from stack
geometry or a separate ownership law.

## Next Test

The next nonredundant scanner should consume the actual unique witness codeword and force one of
its geometric profiles: exact zero-agreement fiber, support denominator, or stack-ownership
collision.  If this scanner can construct a large-zero safe line with a genuine singleton witness,
it refutes the factor-two multiplicity route; if every such singleton is geometrically impossible,
the no-unique-witness socket becomes a real discount.
