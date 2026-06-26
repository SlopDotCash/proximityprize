# delta* #464: same-color relation no-go

Date: 2026-06-26.

Status: negative Lean brick, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The color-cover certificate is only useful when equal colors force a genuinely new algebraic
relation whose fibers can be bounded.  The naive specialization

```text
R(gamma,gamma') := chi(gamma) = chi(gamma')
```

does not help.  If singleton witnesses are independent for this same-color relation, then `chi`
is injective on the singleton-witness fiber.  Consequently the color image has exactly the same
cardinality as the original fiber.

## Lean Surface

`LineListCodewordSingletonRelationColorNoGo.lean` adds the finite collapse:

```lean
scalarSameColorRelation
scalarRelationIndependent_sameColorRelation_iff_injOn
scalarSameColorRelation_image_card_eq_of_independent
```

and the uniform singleton-route version:

```lean
codewordSingletonWitnessScalars_image_card_eq_of_sameColor_forbidden
scalarRelationColorForcesEdges_sameColorRelation
sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden
not_sameColorRelationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden
```

The central equivalence is the concrete same-color instance of the generic collapse in
`LineListCodewordSingletonRelationColorCover.lean`: under the forbidden-edge hypothesis, any
edge-forcing color is injective on the singleton-witness fiber.  For the same-color relation, the
uniform bounded-color certificate is therefore equivalent to the original direct singleton
budget:

```text
UniformLargeZeroSafeCodewordRelationColorBudgeted(sameColor chi, chi, S)
  <-> UniformLargeZeroSafeCodewordSingletonBudgeted(S).
```

The reverse direction is only `Finset.card_image_le` plus the automatic equal-color forcing
condition.  The forward direction is the existing color-cover consumer plus forbidden edges.
The failure theorem says the negative case is also unchanged: it returns exactly a large-zero
safe appearing codeword whose singleton-witness fiber has cardinality above `S`.

## Consequence

This rules out a tempting but vacuous color invariant route.  If the relation is just equality of
the invariant, then the forbidden-edge theorem says the invariant has no collisions among true
singleton witnesses.  The number of colors cannot be smaller than the number of singleton
scalars, so the certificate cannot compress the obstruction.

Future color invariants must do more:

```text
same chi-value
  -> a separate interpolation, second-witness, or exceptional-pencil relation
```

and that separate relation must have small color fibers on the actual singleton-witness sets.

## Verdict

The bounded-color interface remains useful, but its first obvious instantiation is formally a
tautology.  This narrows the live target to nontrivial algebraic color collisions, not
same-color edges.
