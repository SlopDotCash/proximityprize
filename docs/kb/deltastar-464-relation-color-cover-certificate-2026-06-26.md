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
scalarRelationCliqueCover_of_colorForcesEdges
UniformLargeZeroSafeCodewordRelationColorBudgeted
uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted
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
