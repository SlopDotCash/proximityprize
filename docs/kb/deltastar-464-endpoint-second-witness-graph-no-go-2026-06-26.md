# delta* #464: endpoint second-witness graph is admissible but tautological

## Thesis

The most direct "second witness" graph does not give a new scalar saving.  If two singleton
scalars for a fixed codeword `c` are connected when either endpoint already has a distinct second
codeword witness, then the forbidden-edge condition is automatic: singleton witnesses are defined
precisely by the absence of such a second endpoint witness.

That makes the graph formally admissible, but also empty on the actual singleton-witness vertex
set.  Its witness-local independence budget is therefore equivalent to the original per-codeword
singleton cap.

## What was formalized

`LineListCodewordSingletonSecondWitnessRelation.lean` defines:

```lean
codewordEndpointSecondWitnessRelation
```

For fixed `dom k a u0 u1 c`, this relation says that a pair `(gamma, gamma')` is adjacent if
either `gamma` or `gamma'` has some `c' != c` in its `badScalarWitnessCodewords` fiber.

Lean proves the endpoint obstruction directly from uniqueness:

```lean
not_exists_endpointSecondWitness_left_of_mem_codewordSingletonWitnessScalars
not_codewordEndpointSecondWitnessRelation_of_mem_codewordSingletonWitnessScalars
uniformLargeZeroSafeCodewordSingletonRelationForbidden_endpointSecondWitnessRelation
```

The important no-go is the exact equivalence:

```lean
endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted
```

The reverse direction uses the generic lemma now added to
`LineListCodewordSingletonSupportRatio.lean`:

```lean
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_codewordSingletonBudgeted
```

Any direct cap on `codewordSingletonWitnessScalars` bounds every witness-local independent subset,
for any proposed relation.

## Consequence

Endpoint second-witness adjacency is not the missing interpolation graph.  It spends only the
definition of singleton-ness, so it produces no compression among singleton scalars.  The needed
relation has to use pairwise or higher-order structure: two or more singleton scalars must force a
new witness, an RS interpolation dependence, or an explicitly classified exceptional pencil.

The endpoint relation is still useful as a sanity check on the graph API.  It proves the interface
can express a second-witness idea and then classifies the naive endpoint version as a tautology.
