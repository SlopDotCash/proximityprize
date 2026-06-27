# Issue #464: high-multiplicity weight decomposition pin

Date: 2026-06-26.

Status: **exact incidence identity**, not a delta-star floor proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Lean Surface

File:

```text
ArkLib/Data/CodingTheory/ProximityGap/HighMultiplicityBadCount.lean
```

Existing high-multiplicity incidence layer:

```lean
mult
sum_mult_eq_weight
card_highMult_mul_le
highMult_empty_of_lt
weight_e1_le_mult_add_weightLine
weightLine_le_imp_highMult
badWeight_card_mul_le
```

This pass adds:

```lean
ArkLib.ProximityGap.HighMultiplicity.weightLine_add_mult_eq_weightE1_add_zeroE1Nonzero
```

## Content

For every affine error line `e0 + gamma * e1`, the line-word weight plus the root multiplicity on
`supp e1` is constant:

```text
weight(e0 + gamma*e1) + mult(gamma)
  = weight(e1) + #{i : e1 i = 0 and e0 i != 0}.
```

The correction term is independent of `gamma`.  On coordinates with `e1 i != 0`, each coordinate
contributes to exactly one of the two sides: either the affine line vanishes there and contributes
to `mult(gamma)`, or it is nonzero and contributes to the line weight.  On coordinates with
`e1 i = 0`, the line weight contributes exactly the fixed nonzero positions of `e0`.

## Prize Impact

This sharpens the bookkeeping behind `weight_e1_le_mult_add_weightLine` and
`badWeight_card_mul_le`: the high-multiplicity bridge is not losing a hidden gamma-dependent
zero-fiber term.  The only extra term is the fixed `e1 = 0, e0 != 0` contribution, so the
per-error-line bad-scalar count remains a clean ratio-census problem.

It does **not** close the smooth-domain floor.  The open step is still global: after applying the
per-line incidence bound, one must control the in-window codeword-pair/list supply, or prove a
structural multiplicity cap strong enough to make the bad-scalar set empty at the prize radius.

## Validation

```text
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/HighMultiplicityBadCount.lean
./scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.HighMultiplicityBadCount
```

The new theorem's audit line reports only the standard Lean axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
