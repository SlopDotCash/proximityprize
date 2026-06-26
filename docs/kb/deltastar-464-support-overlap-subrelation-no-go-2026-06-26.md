# delta* #464: support-overlap-local relations are edgeless

Date: 2026-06-26.

Status: negative structural theorem, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The singleton graph route asks for a relation on singleton scalars that is dense enough to prove
a small independence number, but still forbidden on true singleton witnesses.  A natural next
attempt is to make edges from local support-ratio geometry: two scalars are adjacent only when
their moving support-ratio fibers share a coordinate, or when a proposed interpolation certificate
first factors through such a shared coordinate.

That entire family is now formalized as a no-go.  For one fixed codeword `c`, the map

```text
i |-> (c i - u0 i) / u1 i
```

is a function on the moving support.  Therefore distinct scalars have disjoint fibers.  If every
edge of a proposed relation implies support-ratio fiber overlap, then the relation has no edge
between distinct scalars at all.  Every finite scalar set is independent.

So the route collapses:

```text
edge implies support-ratio overlap
  -> witness-local graph budget <= S iff direct singleton-fiber budget <= S.
```

This rules out coordinate-local pairwise interpolation as a source of compression.  The missing
edge must use information that does not factor through a shared moving coordinate: a genuine RS
dependence, a second witness away from the endpoints, or an explicitly classified exceptional
pencil.

## Lean Surface

`LineListCodewordSingletonSupportOverlapRelation.lean` now records the generic form:

```lean
CodewordRelationImpliesSupportRatioOverlap
not_codewordRelation_of_supportRatioOverlap_of_ne
scalarRelationIndependent_of_supportRatioOverlapSubrelation
uniformSingletonRelationForbidden_of_supportRatioOverlapSubrelation
supportRatioOverlapSubrelationWitnessBudgeted_iff_singletonBudgeted
not_supportRatioOverlapSubrelationWitnessBudgeted_iff_exists_singleton_card_gt
```

The earlier literal overlap graph remains the special case:

```lean
supportRatioFiberOverlapRelation
uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted
```

## Critique

The previous live target was "invent a pairwise interpolation/color invariant."  The new theorem
separates two meanings of pairwise:

```text
coordinate-local pairwise evidence:
  a shared moving coordinate, shared support-ratio fiber, or a relation implying one.

algebraic pairwise evidence:
  two singleton scalars jointly force another RS codeword, a determinant vanishing, or a pencil
  classification.
```

The first meaning is exhausted.  It is not merely weak; it is edgeless on distinct scalars.

The second meaning is still the live target.  Any useful relation must prove adjacency from a
combined interpolation constraint that survives the disjointness of the support-ratio fibers.
This is a higher bar: it has to spend the uniqueness of `c` as a witness, not just the coordinate
sets on which `c` agrees with line words.

## Consequence

Future singleton graph attempts should fail a quick test before formalization:

```text
Can the proposed edge occur when all moving support-ratio fibers are disjoint?
```

If the answer is no, it is covered by the support-overlap-local no-go.  If the answer is yes,
the edge is genuinely algebraic and belongs in the clique/color interface as the next candidate.
