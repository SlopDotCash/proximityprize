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
badScalarWitnessCodewords_card_pos_of_mem_lineBadScalars
lineBadScalarMultiplicityFloor_one
not_lineBadScalarMultiplicityFloor_two_iff_exists_unique_badScalarWitness
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

The next nonredundant scanner should look for large-zero safe lines where a bad scalar has exactly
one or very few witnessing codewords.  Such a counterexample would refute the multiplicity route in
the same way `LineListArithmeticObstruction.lean` refuted the raw field-power coordinate-fiber
envelope.
