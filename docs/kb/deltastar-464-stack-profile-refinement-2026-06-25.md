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
not_fineFiberMaxReps_iff_exists_bad_used_fineProfile
fineFiberMaxReps_iff_no_bad_used_fineProfile
not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
deltaStar_pin_of_no_bad_fineProfile_scanner
worstCaseIncidenceBounded_iff_no_usedFineProfile_budget_lt_of_fineFiberMaxReps
not_worstCaseIncidenceBounded_iff_exists_usedFineProfile_budget_lt_of_fineFiberMaxReps
worstCaseIncidenceBounded_iff_no_usedFineProfile_budget_lt_of_no_bad_fineProfile
not_worstCaseIncidenceBounded_iff_exists_usedFineProfile_budget_lt_of_no_bad_fineProfile
deltaStar_pin_of_refinedProfileMaxesBounded
not_refinedProfileMaxesBounded_of_counterStack
not_worstCaseIncidenceBounded_of_fineProfile_budget_lt
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

## Continuation: exact scanner certificates

The refinement route now has the same scanner-facing shape as the profile-fiber route:

```lean
not_fineFiberMaxReps_iff_exists_bad_used_fineProfile
fineFiberMaxReps_iff_no_bad_used_fineProfile
```

Failure to choose exact fine-fiber representatives is equivalent to finding a used fine profile
where either:

```text
fine (rep q) != q
```

or a same-fine-profile stack has a larger bad-scalar count than `rep q`.

The grouped budget condition is also exact:

```lean
not_refinedProfileMaxesBounded_iff_exists_usedFineProfile_budget_lt
refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
```

So a refined profile proof can now be certified by two finite absence checks:

```text
no used fine profile has an invalid or beaten representative;
no used fine-profile representative exceeds the budget.
```

Lean packages that as:

```lean
worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
deltaStar_pin_of_no_bad_fineProfile_scanner
```

This does not prove the floor.  It removes ambiguity from iterative classification searches:
after splitting a hard coarse profile into finer fibers, the remaining task is an explicit local
scanner certificate, not another global worst-case argument.  Once that certificate includes the
scaled MCA budget, the delta-star lower pin follows directly at the substrate layer; any later
floor-localization wrapper is only useful if it supplies the budget without assuming this scanner.

## Continuation: universal incidence iff after fine max scanner

The refined route now has the same exact post-max form as the plain profile route:

```lean
worstCaseIncidenceBounded_iff_no_usedFineProfile_budget_lt_of_fineFiberMaxReps
not_worstCaseIncidenceBounded_iff_exists_usedFineProfile_budget_lt_of_fineFiberMaxReps
worstCaseIncidenceBounded_iff_no_usedFineProfile_budget_lt_of_no_bad_fineProfile
not_worstCaseIncidenceBounded_iff_exists_usedFineProfile_budget_lt_of_no_bad_fineProfile
```

After the fine-fiber representative scanner has passed, the original universal stack incidence
budget is equivalent to the absence of an above-budget used fine-profile representative.  The
negative direction is equally local: a failed universal budget is exactly one used fine-profile
label `q` with

```text
B < StackBadCount(rep q).
```

The single-label refuter

```lean
not_worstCaseIncidenceBounded_of_fineProfile_budget_lt
```

packages the same obstruction without needing the grouped refinement hypotheses.  This is still a
reduction, not the floor proof: it says precisely what a successful refined catalogue must certify
after the representative-max step.
