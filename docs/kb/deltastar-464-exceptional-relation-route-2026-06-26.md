# delta* #464: exceptional-set singleton relation route

Date: 2026-06-26.

Status: structural production/scanner interface; not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The pure forbidden-edge graph route collapses to the original singleton cap: if every true
singleton scalar is independent, a graph certificate is not a weaker theorem statement.  The new
exceptional-set route records the next honest relaxation.

A relation may now have edges on a classified exceptional set `Xi`.  Outside `Xi`, singleton
scalars must be relation-independent; inside `Xi`, the exceptional residue is budgeted separately.
The resulting per-codeword singleton cap is `S + E`: `S` for the non-exceptional good part and
`E` for exceptional singleton scalars.

## Lean Surface

`LineListCodewordSingletonRelationException.lean` exposes:

```lean
scalarRelationIndependentOutside
not_scalarRelationIndependentOutside_iff_exists_edge
scalarRelation_card_le_goodIndependence_add_exception
UniformLargeZeroSafeCodewordRelationForbiddenOutside
UniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted
UniformLargeZeroSafeCodewordRelationExceptionBudgeted
UniformLargeZeroSafeCodewordGoodOutsideBudgeted
uniformLargeZeroSafeCodewordRelationGoodIndependenceBudgeted_of_goodOutsideBudgeted
uniformLargeZeroSafeCodewordGoodOutsideBudgeted_of_relationGoodIndependence
relationGoodIndependenceBudgeted_iff_goodOutsideBudgeted_of_forbiddenOutside
uniformLargeZeroSafeCodewordSingletonBudgeted_of_goodOutside_and_exception
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationGoodIndependenceOutside
not_uniformLargeZeroSafeCodewordRelationForbiddenOutside_iff_exists_edge
exists_largeZero_safe_codewordRelationGoodIndependent_gt_of_not_goodIndependence
not_uniformLargeZeroSafeCodewordRelationExceptionBudgeted_iff_exists_card_gt
not_uniformLargeZeroSafeCodewordGoodOutsideBudgeted_iff_exists_card_gt
exists_largeZero_safe_codewordPartitionBudgetFailure_of_not_codewordSingletonBudgeted
exists_largeZero_safe_codewordRelationException_gt_of_not_codewordSingletonBudgeted
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationException
exists_largeZero_safe_codewordRelationExceptionRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordPartitionRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordRelationExceptionRouteObstruction_of_not_budgeted
```

The scanner exposes four finite failure modes:

```text
1. a forbidden relation edge outside Xi,
2. an overlarge independent good subset outside Xi,
3. the usual punctured-weight plus singleton-cap arithmetic failure,
4. too many exceptional singleton scalars for one appearing codeword.
```

The good-side independence budget also has a direct collapse theorem.  Once outside edges are
forbidden, bounding all independent good subsets is equivalent to directly bounding the
non-exceptional singleton set `codewordSingletonWitnessScalars \ Xi`.  The partition theorem
`uniformLargeZeroSafeCodewordSingletonBudgeted_of_goodOutside_and_exception` records the resulting
direct `good + exception` cap without mentioning a relation.

The direct partition split has its own exact scanner:

```lean
not_uniformLargeZeroSafeCodewordGoodOutsideBudgeted_iff_exists_card_gt
exists_largeZero_safe_codewordPartitionBudgetFailure_of_not_codewordSingletonBudgeted
exists_largeZero_safe_codewordPartitionRouteFailure_of_not_budgeted
```

So for any fixed exceptional set `Xi`, failure of the `S + E` singleton cap forces a concrete
appearing codeword whose non-exceptional part exceeds `S` or whose exceptional part exceeds `E`.
This removes the relation from the last accounting step; after the outside edge condition is
known, the route is just a finite partition budget.  At the line-budget production layer, the same
scanner exposes this partition failure or the usual punctured-weight arithmetic failure.

## Consequence

This does not close the singleton branch, but it makes the next possible graph theorem precise.
A useful relation must now classify and budget the exceptions that were previously hidden inside
the forbidden-edge hypothesis.  Pure graph packaging still does not help unless the exceptional
set is algebraically small and the complementary singleton set has its own genuine cardinality
bound.
