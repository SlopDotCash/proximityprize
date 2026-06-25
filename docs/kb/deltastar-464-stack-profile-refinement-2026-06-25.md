# Issue #464: stack-profile refinement bridge

Date: 2026-06-25.

Status: **classification bookkeeping**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackProfileRefinement.lean
```

records how to refine a coarse stack profile into a finer one.

Given

```lean
fine : WordStack A (Fin 2) iota -> Q
coarse : WordStack A (Fin 2) iota -> P
project : Q -> P
```

the refinement condition is

```lean
ProfileRefines fine coarse project
```

meaning `project (fine u) = coarse u` for every stack `u`.

Lean proves the main consumer:

```lean
worstCaseIncidenceBounded_of_refinedProfileMaxesBounded
worstCaseIncidenceBounded_iff_refinedProfileMaxesBounded
deltaStar_pin_of_refinedProfileMaxesBounded
not_refinedProfileMaxesBounded_of_counterStack
not_fineFiberMaxRep_of_sameFineProfile_strictly_larger
```

## The Exact Reduction

If every used fine-profile fiber has a chosen bad-scalar maximizer, then the universal incidence
bound is equivalent to bounding those fine-profile maximizers, grouped over the used coarse
profiles.

This is the output type for an iterative classification search:

```text
start with a coarse profile;
split hard coarse fibers into finer fibers;
prove the maximizer in every used fine fiber is within budget.
```

The file also includes the identity-profile sanity check.  If the fine profile is just the stack
itself, the refined-profile condition collapses back to the original all-stack incidence bound.

## Critical Consequence

Refinement is useful only when the fine profile creates fibers whose maximizers can be controlled by
structure.  Refinement by itself does not reduce the problem; it merely names where the problem has
moved.

The red-team test is local:

```text
find a stack above budget, or
find a same-fine-profile stack with a larger bad-scalar count than the proposed representative.
```

Either witness kills the proposed refined-profile route at the exact point where it claims to have
compressed the worst-case stack search.
