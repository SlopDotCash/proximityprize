# Issue #464: profile fibers expose the exact classification target

Date: 2026-06-25.

Status: **classification target sharpened**, not a delta-star proof.

## What Was Formalized

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_StackProfileFiberMax.lean
```

adds the missing internal max layer for profile-based attacks.

Given a profile map

```lean
profile : WordStack A (Fin 2) iota -> P
```

the file defines the finite fiber

```lean
profileFiber profile p
```

and the exact maximizer predicate

```lean
ProfileFiberMax F C delta profile p uMax
```

meaning `uMax` has profile `p` and dominates every stack with profile `p` for the actual MCA
bad-scalar count.

Lean proves:

```lean
exists_profileFiberMax_of_used
worstCaseIncidenceBounded_iff_profileFiberMaxesBounded
familyDominates_of_profileFiberMaxReps
deltaStar_pin_of_profileFiberMaxesBounded
not_profileFiberMax_of_sameProfile_strictly_larger
```

## The Exact Reduction

For any used profile `p`, the profile fiber is finite, so it has a true worst stack.

Therefore a profile-classification proof of

```text
WorstCaseIncidenceBounded C delta B
```

is exactly equivalent to:

```text
for every used profile p, the worst stack in the p-fiber has bad-scalar count <= B.
```

This is stronger and cleaner than saying "each profile has a convenient representative."  The
representative must be a profile-fiber maximizer, or it must dominate that fiber by a separate
theorem.

## Refutation Test

The local falsification criterion is:

```text
find uWitness with the same profile as uCand and
StackBadCount(uCand) < StackBadCount(uWitness).
```

That kills the claim that `uCand` is the profile-fiber maximizer.  It also prevents a binder/floor
representative from being used as a profile cap unless it is actually worst inside its fiber.

## Critical Verdict

This is the honest shape of a non-BGK classification route:

```text
choose a profile space P that is rich enough that each fiber's true maximizer is analyzable,
but small/structured enough that all fiber maxima can be bounded at prize scale.
```

Too coarse a profile collapses to the global maximizer problem.  The file records this explicitly:
if the profile map is constant, a profile-fiber maximizer is just a global stack maximizer.

Too fine a profile gives no compression; it merely restates the all-stack bound.

So the mathematical burden is now precise.  A useful floor/binder profile must make the worst stack
in every fiber structurally forced, not merely enumerable or aesthetically natural.
