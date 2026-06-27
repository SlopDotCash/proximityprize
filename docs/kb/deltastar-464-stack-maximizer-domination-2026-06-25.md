# Issue #464 loop note: domination means identifying the global maximizer

Date: 2026-06-25.

Status: **interface progress with a warning**, not a delta-star proof.

## What was formalized

The landed module is:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/StackMaximizerDomination.lean
```

The file defines the actual stack bad-scalar count again, locally and standalone:

```lean
StackBadCount F C delta u
StackBounded F C delta u B
StackDominates F C delta uMax
```

Because `WordStack A (Fin 2) iota` is finite, Lean proves:

```lean
exists_stackDominates
```

There is always some stack `uMax` whose bad-scalar count is at least every other stack's count.

For such a stack, the universal open-core bound is equivalent to bounding that one stack:

```lean
worstCaseIncidenceBounded_iff_stackBounded_of_stackDominates
exists_singleStackDominationCertificate_iff_worstCaseIncidenceBounded
```

and the delta-star consumer is:

```lean
deltaStar_pin_of_stackMaximizer
```

The file also records the refutation interface:

```lean
not_stackBounded_iff_budget_lt_stackBadCount
not_stackDominates_of_exists_strictly_larger
not_worstCaseIncidenceBounded_of_budget_lt_stackBadCount
not_worstCaseIncidenceBounded_iff_exists_budget_lt_stackBadCount
not_exists_singleStackDominationCertificate_iff_exists_budget_lt_stackBadCount
candidateBounded_and_counterStack_not_worstCaseIncidenceBounded
candidateBounded_not_dominationProof_of_strictly_larger
```

So an exact scanner can kill a proposed binder/floor dominator by exhibiting one stack with strictly
larger bad-scalar count, or kill a proposed budget by exhibiting one stack above it.

The negative open-core statement is now exact, not merely one-way:

```text
not WorstCaseIncidenceBounded C delta B
  iff some stack has StackBadCount above B.
```

This is the formal shape of every failed floor-prize attempt: the missing theorem is precisely the
exclusion of all above-budget stacks.

The exact certificate theorem says there is no gap between the universal incidence hypothesis and
a bounded true maximizer:

```text
exists uMax, StackDominates uMax and StackBounded uMax B
  iff WorstCaseIncidenceBounded C delta B.
```

Thus a one-stack certificate can be complete, but only if its stack is genuinely a global maximizer.
Failure of every such certificate is equivalently an above-budget stack.

I also added the finite-family version:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackCandidateFamilyMax.lean
```

The main predicates are:

```lean
FamilyBounded F C delta R B
FamilyDominates F C delta R
IsFamilyMax F C delta R rMax
```

The key consumer is:

```lean
worstCaseIncidenceBounded_iff_familyBounded_of_familyDominates
```

and the refutation interface is:

```lean
not_familyDominates_of_exists_strictly_larger_than_all
familyBounded_and_counterStack_not_worstCaseIncidenceBounded
familyBounded_not_dominationProof_of_exists_strictly_larger_than_all
```

A finite binder/floor catalogue is therefore a valid consumer only if every stack is dominated by
some representative in the catalogue.  One witness whose bad-scalar count exceeds every member of
the family refutes the catalogue as a universal replacement for `WorstCaseIncidenceBounded`.

## Why this matters

This resolves a possible conceptual confusion in the floor route.

A one-stack proof is not logically impossible.  The finite stack space always has a worst stack.
If we could bound that stack by `B`, then `WorstCaseIncidenceBounded C delta B` follows exactly.

But this is also the trap: a proposed binder, monomial, or floor-localized stack is useful only if
it is proved to be such a global maximizer or to dominate one.  The nonconstructive theorem chooses
`uMax` after looking at the whole incidence function.  It does not identify `uMax` with the
arithmetically convenient binder stack.

So the surviving off-BGK strategy has this exact missing theorem:

```text
the binder/floor stack is a global maximizer of StackBadCount,
or every global maximizer reduces to that family,
or the binder/floor family dominates all global maximizers.
```

Without one of these, floor-localization remains obstruction removal.

## Critical verdict

The stack-maximizer brick turns the domination problem into a sharply stated classification problem.
It does not reduce the analytic content.  It says:

```text
single-stack proof = proof about the true worst stack.
```

The next mathematical attack cannot be "find a nice stack and bound it."  It must explain why the
true worst stack is nice.

Conversely, the fastest way to refute a candidate binder stack is now explicit:

```text
find uWitness with StackBadCount(uBinder) < StackBadCount(uWitness).
```

For a finite binder/floor family, the scanner target is:

```text
find uWitness with StackBadCount(r) < StackBadCount(uWitness) for every r in R.
```

That does not solve the floor, but it prevents the floor route from silently using a non-maximizing
stack, or non-dominating family of stacks, as if it were universal.

That is exactly the sparse-dominance/classification theorem still missing from issue #464.
