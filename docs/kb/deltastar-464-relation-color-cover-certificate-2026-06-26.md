# delta* #464: color certificates for singleton relation covers

Date: 2026-06-26.

Status: certificate interface, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The clique-cover graph route still needs an algebraic way to produce few cliques on each
singleton-witness fiber.  A natural target is a bounded invariant:

```text
chi(u0,u1,c,gamma)
```

If this invariant takes at most `S` values on the actual singleton scalars for an appearing
codeword, and two distinct singleton scalars with the same invariant value are forced to be
related, then the invariant fibers are relation-cliques.  That gives the witness-local
independence budget.

## Lean Surface

`LineListCodewordSingletonRelationColorCover.lean` adds:

```lean
scalarRelationColorForcesEdges
scalarRelationColorFailure
not_scalarRelationColorForcesEdges_iff_exists_pair
scalarRelationCliqueCover_of_colorForcesEdges
scalarRelationColor_injOn_of_independent_of_forcesEdges
scalarRelationColor_image_card_eq_of_independent_of_forcesEdges
UniformLargeZeroSafeCodewordRelationColorForcesEdges
UniformLargeZeroSafeCodewordRelationColorImageBudgeted
UniformLargeZeroSafeCodewordRelationColorBudgeted
relationColorForcesEdges_of_relationColorBudgeted
relationColorImageBudgeted_of_relationColorBudgeted
relationColorBudgeted_of_imageBudgeted_and_forcesEdges
codewordSingletonColor_image_card_eq_of_forbidden_of_forcesEdges
relationColorImageBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
not_relationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden_of_forcesEdges
not_uniformLargeZeroSafeCodewordRelationColorBudgeted_iff_exists_colorFailure
uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted
exists_largeZero_safe_codewordRelationColorRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordRelationColorRouteObstruction_of_not_budgeted
```

The generic combinatorial theorem is the key:

```text
equal color values force relation edges
  -> color fibers form a clique cover
  -> number of colors bounds independent singleton sets.
```

The uniform wrapper lets the color depend on the line, the appearing codeword, and the scalar.
That is the right shape for interpolation determinants, profile refinements, or exceptional-pencil
labels.

The scanner makes failed attempts concrete.  A failed color certificate returns either too many
color values on one singleton-witness fiber or two distinct singleton scalars with the same color
that do not satisfy the proposed relation.  The full route scanner adds the usual alternatives:
a forbidden relation edge or the arithmetic production failure.

There is also a generic collapse theorem.  If singleton witnesses are forbidden to contain
relation edges and the color really does force relation edges, then the color is injective on the
actual singleton-witness fiber.  Consequently, with the edge-forcing half fixed,
`UniformLargeZeroSafeCodewordRelationColorBudgeted` is equivalent to
`UniformLargeZeroSafeCodewordSingletonBudgeted`; its negated form returns exactly the old
overfull singleton fiber.  The color route is therefore a proof method, not a weaker target.

## Critical Point

This does not weaken the final theorem.  By the generic forbidden-edge collapse, once the
relation is known to have no edges among true singleton witnesses, the witness-local graph budget
is equivalent to the original singleton cap.  The color interface is useful only if the proposed
invariant has a genuinely bounded image on the actual singleton-witness fiber and equal colors
force a real algebraic contradiction.

So the missing theorem is now sharper:

```text
construct chi with small image on codewordSingletonWitnessScalars,
and prove equal-chi singleton pairs force a second witness or an exceptional pencil.
```

If every plausible `chi` has image as large as the singleton fiber, the route has merely renamed
the original obstruction.

`LineListCodewordSingletonRelationColorNoGo.lean` records the first concrete specialization of
that collapse.  For the same-color relation

```text
R(gamma,gamma') := chi(gamma) = chi(gamma')
```

the forbidden-edge hypothesis makes `chi` injective on every singleton-witness fiber.  The theorem
`sameColorRelationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden` says the bounded-color
certificate is exactly equivalent to the original singleton budget.  Thus useful color invariants
must force a separate algebraic relation, not merely their own equality relation.
Its failure form
`not_sameColorRelationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden` returns precisely
the old overfull singleton fiber.
