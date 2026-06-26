# delta* #464: singleton scalar independence graphs

Date: 2026-06-26.

Status: **new tool interface**, not a delta-star proof.

Issue source: https://github.com/lalalune/ArkLib/issues/464.

## Thesis

The fixed-codeword support-ratio cover has reached the end of what pure coordinate packing can
do.  For one codeword `c`, distinct singleton scalars have disjoint support-ratio fibers, and the
positive-deficit cover already injects into ambient moving-support subsets.  That is a useful
accounting theorem, but it is not the scalar cap needed for the floor.

The next plausible object is a graph on singleton scalars.  An edge should mean:

```text
the two singleton scalars are algebraically incompatible unless a second witness appears
or the line belongs to an explicitly classified exceptional pencil.
```

The new Lean interface makes that idea falsifiable.  It separates the proof into two obligations:

```text
1. Forbidden-edge theorem:
   true singleton scalars form an independent set for the proposed relation.

2. Independence-number theorem:
   every independent subset of the singleton-witness set has size at most S.
```

Together those imply the existing per-codeword singleton cap, and therefore plug into the current
support-adjusted production route.

## New Machine Surface

`LineListCodewordSingletonSupportRatio.lean` now contains:

```lean
scalarRelationIndependent
not_scalarRelationIndependent_iff_exists_edge
UniformLargeZeroSafeCodewordSingletonRelationForbidden
not_uniformLargeZeroSafeCodewordSingletonRelationForbidden_iff_exists_edge
UniformLargeZeroSafeCodewordRelationIndependenceBudgeted
UniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted
uniformLargeZeroSafeCodewordRelationWitnessIndependenceBudgeted_of_relationIndependence
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationIndependence
uniformLargeZeroSafeCodewordSingletonBudgeted_of_relationWitnessIndependence
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationIndependence
uniformLineBadScalarsBudgeted_of_supportAdjusted_and_codewordRelationWitnessIndependence
exists_largeZero_safe_codewordRelationWitnessIndependent_gt_of_not_relationWitnessIndependence
exists_largeZero_safe_codewordRelationIndependent_gt_of_not_codewordSingletonBudgeted
exists_largeZero_safe_codewordRelationIndependentRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordRelationWitnessIndependentRouteFailure_of_not_budgeted
exists_largeZero_safe_codewordRelationWitnessRouteObstruction_of_not_budgeted
```

The relation has type:

```lean
(Fin n -> F) -> (Fin n -> F) -> (Fin n -> F) -> F -> F -> Prop
```

so it may depend on the line `(u0,u1)`, the appearing codeword `c`, and the two scalars.  This is
deliberately broad.  A useful relation might be an interpolation determinant edge, a shared
second-witness forcing edge, or an exceptional-pencil exclusion edge.  The interface does not
pretend to know which one is true.

There are two independence budgets.  The global one asks for every independent scalar finset to
be small.  That is often stronger than the mathematics should need.  The witness-local one only
asks for independent subsets of

```text
codewordSingletonWitnessScalars(dom,k,a,u0,u1,c)
```

and is the intended target for future graph theorems.  The global budget still implies the
witness-local budget, so it remains a convenient sufficient condition.

The consumer is exact:

```text
forbidden singleton graph + witness-local independence cap
  -> UniformLargeZeroSafeCodewordSingletonBudgeted
  -> existing singleton-cap production route.
```

The scanner is also exact.  If support-side hypotheses are fixed, the forbidden-edge half is
available, and production still fails, Lean returns either:

```text
1. the usual punctured-weight plus appearing-codeword arithmetic failure, or
2. one large-zero safe line, one appearing codeword, and an independent subset of that
   codeword's singleton scalars above the proposed cap S.
```

That second object is the right counterexample to any proposed interpolation graph.
The full scanner removes the forbidden-edge assumption:

```lean
exists_largeZero_safe_codewordRelationWitnessRouteObstruction_of_not_budgeted
```

It returns one of three concrete obstructions: an actual relation edge between two singleton
witness scalars, the usual arithmetic failure, or an over-cap independent subset of singleton
scalars.  Thus a proposed relation has both halves exposed by finite witnesses.

## Why This Is Better Than Another Cover Bound

The previous cover counts pairs `(gamma,T)`.  Even after removing the field/scalar factor, the
best pure packing theorem counts subsets:

```text
#cover(c) <= choose(#support(u1), a - #zeroAgreement(c)).
```

The floor needs a bound on scalars:

```text
#codewordSingletonWitnessScalars(c) <= S.
```

Counting subsets cannot normally deliver that.  A scalar graph can: if many singleton scalars
exist, the graph theorem must produce an edge among them, and the forbidden-edge theorem then
forces a second witness or an exceptional certificate.  This is the first interface in this lane
that attacks scalars directly instead of paying for their possible support subsets.
The witness-local budget is important here: it avoids proving a graph theorem for arbitrary field
subsets when the production route only needs subsets of the actual singleton-witness set.

## Immediate Refutation Pressure

The empty relation is useless: every set is independent, so the independence-number theorem would
be as hard as the original singleton cap.  The coordinate-overlap relation is also useless for a
fixed codeword, because distinct support-ratio fibers are disjoint.  That failure is already
formalized by the support-ratio partition lemmas and now by the explicit graph no-go

```lean
uniformRelationWitnessIndependenceBudgeted_supportRatioFiberOverlap_iff_singletonBudgeted
```

The endpoint second-witness relation fails in the opposite but equally vacuous way: singleton
witnesses rule out second witnesses at each endpoint by definition, so the forbidden-edge theorem
is automatic and the witness-local budget again collapses to the original singleton cap:

```lean
endpointSecondWitnessRelationWitnessBudgeted_iff_codewordSingletonBudgeted
```

So a viable relation must be genuinely algebraic.  It has to spend information that coordinate
packing throws away:

```text
- both line words come from the same affine pencil;
- c is the unique heavy RS codeword at each singleton scalar;
- another low-degree polynomial agreeing on the combined constraints would be a second witness;
- exceptional pencils can be stated and isolated explicitly.
```

If a proposed relation cannot prove a small independence number without reusing the BGK/Paley
sup-norm bound, it is only a renamed wall.  The new scanner will expose this by returning a large
independent set of singleton scalars.
If the relation is too dense or semantically wrong, the forbidden-edge iff exposes the other
failure mode by returning two distinct singleton scalars that are connected by the relation.

## Candidate Relations To Attack

1. **Interpolation determinant edge.**
   Connect `gamma` and `gamma'` when selected subfibers from their support-ratio covers force a
   low-degree interpolant through the union of constraints.  The forbidden-edge theorem would say
   that such an interpolant is a second witness, contradicting singleton uniqueness.

2. **Second-witness forcing edge.**
   Connect two scalars when their heavy agreement sets have enough algebraic overlap in the
   polynomial coefficient space to produce a distinct codeword heavy at one of them.  This is
   closer to `BadScalarSecondWitnessProperty`, but localized to one codeword's singleton fiber.

3. **Exceptional-pencil complement.**
   Define edges outside a classified exceptional family.  Then an overlarge independent set says
   the line is trapped inside the exceptional family.  The production theorem would need a
   separate budget for that family.

4. **Profile-refined graph.**
   Let the relation depend on the exact zero-agreement profile
   `directionZeroAgreementSet c u0 u1`.  The support-ratio partition says only the profile size
   matters for packing; a graph theorem may use the actual profile.

## Critique

This does not solve the floor.  It gives the next proof attempt a real contract.

The danger in this problem is to produce another elegant equivalent form of the same hard
quantity.  A graph relation avoids that only if it proves both halves:

```text
forbidden edges among singleton witnesses
small independent subsets of the singleton-witness set for the relation
```

Proving only the first half is cheap if the relation is too dense or semantically impossible.
Proving only the second half is cheap if the relation is too strong or unrelated to singleton
witnesses.  The two halves together are the test.

## Verdict

The independence-graph tool is the right shape for the next non-coordinate attack on the
singleton-cap route.  It does not bypass the BGK/Paley wall by itself.  Its value is that every
future scalar-rigidity proposal now has a Lean-facing consumer and a Lean-facing falsifier:

```text
either prove the relation has small independent sets and forbidden singleton edges,
or produce an overlarge independent subset of singleton scalars and learn exactly why the graph
failed; if the forbidden-edge half is false, produce an actual edge among singleton witnesses.
```
