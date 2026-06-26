# delta* #464: two singleton graph candidates refuted

Date: 2026-06-26.

Status: **negative Lean result**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The singleton-scalar graph interface is useful only if a proposed relation has real edges while
remaining forbidden on true singleton witnesses.  Two tempting first relations fail that test.

First, coordinate overlap of fixed-codeword support-ratio fibers is edgeless.  A coordinate in
the moving support has exactly one ratio

```text
(c i - u0 i) / u1 i
```

so distinct scalars cannot share a support-ratio fiber coordinate for the same codeword.  This
means the coordinate-overlap graph supplies no independence saving: every singleton-scalar subset
is independent.

Second, the endpoint second-witness relation is also vacuous on singleton-witness scalars.  It
connects scalars when one endpoint already has a distinct second codeword witness, but the
definition of `codewordSingletonWitnessScalars` rules that out at each endpoint.  Thus it proves
the forbidden-edge half immediately and gives no compression unless one already has the original
per-codeword singleton cap.

## What was formalized

`LineListCodewordSingletonSupportOverlapRelation.lean` names the coordinate-overlap graph:

```lean
supportRatioFiberOverlapRelation
not_supportRatioFiberOverlapRelation_of_ne
scalarRelationIndependent_supportRatioFiberOverlapRelation
uniformLargeZeroSafeCodewordSingletonRelationForbidden_supportRatioFiberOverlap
uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted
```

The last theorem is the important no-go statement.  For this relation, the witness-local
independence budget is exactly equivalent to the original
`UniformLargeZeroSafeCodewordSingletonBudgeted` obligation.  The relation has no distinct-scalar
edges, so the graph theorem would only reprove the cap it was meant to replace.

`LineListCodewordSingletonSecondWitnessRelation.lean` records the analogous endpoint
second-witness no-go:

```lean
codewordEndpointSecondWitnessRelation
not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
not_codewordEndpointSecondWitnessRelation_of_mem_codewordSingletonWitnessScalars
uniformLargeZeroSafeCodewordSingletonRelationForbidden_endpointSecondWitnessRelation
endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted
```

Again, the equivalence theorem is the critical verdict.  A relation that only asks whether an
endpoint already has a second witness cannot compress the singleton fiber, because singleton
witnesses are defined by the absence of such endpoints.

The generic reason is now recorded in the base interface:

```lean
relationWitnessIndependenceBudgeted_iff_codewordSingletonBudgeted_of_forbidden
not_relationWitnessIndependenceBudgeted_iff_exists_singleton_card_gt_of_forbidden
```

Under any forbidden-edge theorem, a witness-local graph budget is extensionally the same
obligation as the original singleton cap.  A relation still matters as a proof strategy only if
it supplies a genuinely new way to prove that budget.

## Consequence

These failures are good filters.  A useful singleton graph cannot be:

```text
- raw coordinate overlap inside one fixed support-ratio partition, or
- a predicate that is already pointwise false for every singleton endpoint.
```

The next relation has to be genuinely algebraic.  It should connect two singleton scalars when
their combined interpolation constraints force a second witness, force a low-dimensional
exceptional pencil, or violate an independently provable RS rigidity condition.  The edge must use
information from the pair, not merely an endpoint property that singleton uniqueness already
forbids.

## Verdict

The graph interface remains the right contract, but these two candidates are formally exhausted.
The live target is a pairwise interpolation or exceptional-pencil relation with nontrivial
independence-number content on `codewordSingletonWitnessScalars`.
