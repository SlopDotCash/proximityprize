# delta* #464: clique-cover certificate for singleton relation graphs

Date: 2026-06-26.

Status: certificate interface, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The witness-local singleton graph route needs a concrete way to prove that every independent
subset of `codewordSingletonWitnessScalars` has size at most `S`.  A standard finite-graph
certificate is now available: cover the singleton-witness set by at most `S` relation-cliques.
Any independent set meets each clique in at most one vertex.

This does not propose the missing algebraic relation.  It gives future interpolation or
exceptional-pencil relations a precise finite certificate to target.

## Lean Surface

`LineListCodewordSingletonRelationCliqueCover.lean` defines the finite graph primitives:

```lean
scalarRelationClique
scalarRelationCliqueCover
scalarRelationIndependent_inter_clique_card_le_one
scalarRelationIndependent_card_le_of_cliqueCover
scalarRelationCliqueCover_singletons
scalarRelationCliqueCover_card_ge_of_independent
```

and the uniform singleton-route certificate:

```lean
UniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationCliqueCover
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationCliqueCover
uniformRelationCliqueCoverBudgeted_of_codewordSingletonBudgeted
relationCliqueCoverBudgeted_iff_codewordSingletonBudgeted_of_forbidden
not_relationCliqueCoverBudgeted_iff_exists_singleton_card_gt_of_forbidden
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationCliqueCover
```

The scanner surface is explicit:

```lean
not_uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_iff_exists_no_cover
exists_largeZero_safe_codewordRelationCliqueCoverRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordRelationCliqueCoverRouteObstruction_of_not_budgeted
```

Failed production now exposes one of three objects:

```text
1. an actual forbidden relation edge among singleton witnesses,
2. the usual combined arithmetic failure, or
3. a large-zero safe appearing codeword whose singleton-witness fiber has no at-most-S clique cover.
```

`deltastar-464-clique-cover-collapse-2026-06-26.md` records the matching collapse theorem.  Under
forbidden edges, every clique intersects the singleton-witness fiber in at most one scalar, while
the singleton cover always exists if the direct scalar cap is already true.  Hence the
clique-cover budget is equivalent to the original singleton-fiber budget once forbidden edges are
fixed.

`LineListCodewordSingletonRelationColorCover.lean` adds a convenient way to build such clique
covers from bounded invariants:

```lean
scalarRelationColorForcesEdges
scalarRelationColorFailure
scalarRelationCliqueCover_of_colorForcesEdges
relationColorBudgeted_iff_codewordSingletonBudgeted_of_forbidden_of_forcesEdges
not_relationColorBudgeted_iff_exists_singleton_card_gt_of_forbidden_of_forcesEdges
UniformLargeZeroSafeCodewordRelationColorBudgeted
uniformLargeZeroSafeCodewordRelationCliqueCoverBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationColorBudgeted
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationColorBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationColorBudgeted
exists_largeZero_safe_codewordRelationColorRouteObstruction_of_not_budgeted
```

If equal colors force relation edges on the singleton-witness fiber, then color fibers are
relation-cliques.  Bounding the number of colors therefore bounds the witness-local independence
number.  If the route fails, the color scanner returns too many colors or a same-color non-edge
on a concrete large-zero safe appearing codeword.

The first naive color specialization has now been ruled out.  In
`LineListCodewordSingletonRelationColorNoGo.lean`, taking the relation itself to be equality of
colors forces the color map to be injective on every singleton-witness fiber under the
forbidden-edge hypothesis.  The resulting certificate is equivalent to the original direct
singleton cap, so it cannot supply a smaller clique cover.

## Consequence

The graph interface is still not a proof by itself.  The generic forbidden-edge collapse says the
witness-local graph budget is equivalent to the original singleton cap once forbidden edges are
known.  The clique-cover certificate is useful because it is a possible proof method for that
budget: find a relation whose singleton vertices can be covered by few algebraic cliques, or find
a bounded invariant whose fibers are those cliques.

The live target is now sharper: produce a non-vacuous pairwise interpolation relation and prove a
small clique/color cover for the actual singleton-witness fibers.
