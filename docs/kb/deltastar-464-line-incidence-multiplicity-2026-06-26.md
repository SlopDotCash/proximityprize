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
not_lineBadScalarMultiplicityFloor_two_iff_exists_uniqueWitnessCodeword
not_noUniqueBadScalarWitness_iff_exists_uniqueWitnessCodeword
lineBadScalarMultiplicityFloor_two_iff_noUniqueBadScalarWitness
lineBadScalars_card_le_puncturedZeroStratifiedLineWeight_div_two_of_noUniqueBadScalarWitness
lineBadScalars_card_le_of_noUniqueBadScalarWitness_and_weight_div_two_le
not_noUniqueBadScalarWitness_iff_exists_unique_badScalarWitness
exists_unique_badScalarWitness_of_not_lineBadScalars_card_le
exists_uniqueWitnessCodeword_of_not_lineBadScalars_card_le
UniformLargeZeroSafeNoUniqueBadScalarWitness
UniformLargeZeroSafePuncturedWeightDivTwoBudgeted
largeZeroSafeLineBadScalarsBudgeted_of_uniformNoUniqueBadScalarWitness_and_puncturedWeightDivTwo
uniformLineBadScalarsBudgeted_of_supportAdjustedBudgetFits_and_noUniqueWitnessPuncturedWeightDivTwo
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

This is still conditional.  The substantive new hard input is a uniform proof that large-zero safe
lines have no unique-witness bad scalar, plus the arithmetic proof that the punctured weight divided
by two fits the target budget.

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
