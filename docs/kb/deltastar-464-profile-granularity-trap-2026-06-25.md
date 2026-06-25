# Issue #464: the profile granularity trap

Date: 2026-06-25.

Status: **guardrail**, not a delta-star proof.

## What Was Added

The file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackProfileFiberMax.lean
```

now records both ends of the profile-classification spectrum:

```lean
stackDominates_of_profileFiberMax_constant
profileFiberMaxReps_identity
profileFiberMaxesBounded_identity_iff_worstCaseIncidenceBounded
```

The constant-profile theorem says that if all stacks have the same profile, then a profile-fiber
maximizer is just a global stack maximizer.

The identity-profile theorem says that if every stack is its own profile, then the profile-fiber
maximizer construction is tautological, and bounding all profile maxima is exactly the original
universal incidence statement.

## Critical Consequence

A useful profile for the #464 floor cannot be arbitrarily coarse or arbitrarily fine.

```text
too coarse  -> the global worst-stack problem returns unchanged;
too fine    -> the all-stack quantifier returns unchanged.
```

The only possible gain is a middle profile: coarse enough to compress the stack universe, but fine
enough that each fiber's true maximizer is structurally forced and analyzable.

This is a precise red-team test for proposed binder, adjacent-pattern, monomial, orbit, or
floor-localization profiles:

```text
does the profile actually shrink the proof,
or does it secretly ask for the global maximizer / all-stack bound again?
```

If the answer is the latter, it is not a floor proof architecture.
