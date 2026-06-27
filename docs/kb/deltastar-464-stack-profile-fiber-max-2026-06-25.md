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
not_profileFiberMaxReps_iff_exists_bad_used_profile
profileFiberMaxReps_iff_no_bad_used_profile
not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt
profileFiberMaxesBounded_iff_no_usedProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
deltaStar_pin_of_no_bad_used_profile_scanner
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

## Continuation: fiber representatives contain a global maximizer

The profile route now connects directly to the max-containment floor contract:

```lean
exists_usedProfile_stackDominates_of_profileFiberMaxReps
not_profileFiberMaxReps_of_each_used_rep_beaten
```

If `rep p` is an exact fiber maximizer for every used profile, then one used profile representative
is a true global maximizer of the actual bad-scalar count.  The proof is finite but important:
choose a global stack maximizer `uMax`; the representative of `profile uMax` dominates that fiber,
so it has count at least `uMax` and therefore dominates every stack.

The refutation side is also now local:

```text
for every used profile p, find a stack u with
StackBadCount(rep p) < StackBadCount(u).
```

That rules out the claim that the selected representatives are exact profile-fiber maximizers.
Thus a profile proof cannot stop at choosing natural representatives; it must prove those
representatives are actual fiber maxima, or the scanner can refute the choice profile-by-profile.

## Continuation: exact scanner iff

The profile representative check is now an exact finite certificate:

```lean
not_profileFiberMaxReps_iff_exists_bad_used_profile
profileFiberMaxReps_iff_no_bad_used_profile
```

A representative catalogue fails precisely when some used profile has either:

```text
profile(rep p) != p
```

or a same-profile witness `u` with larger bad-scalar count:

```text
profile u = p
StackBadCount(rep p) < StackBadCount(u).
```

Equivalently, exact fiber-max representatives are certified by the absence of these bad used
profiles.  This turns the profile route into a scanner-facing finite proof obligation rather than a
qualitative classification slogan.

The budget side has the same exact scanner shape: chosen used-profile representatives are bounded by
`B` iff the scanner finds no used representative with `B < StackBadCount(rep p)`.  Combining the
max-side and budget-side positive scanners gives the direct incidence consumer
`worstCaseIncidenceBounded_of_no_bad_used_profile_scanner`, before any floor-localization contract is
introduced.  With the scaled MCA budget, `deltaStar_pin_of_no_bad_used_profile_scanner` then gives
the corresponding lower pin directly from scanner evidence.

## Continuation: budget scanner iff

The budget side now has the same exact scanner shape:

```lean
not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt
profileFiberMaxesBounded_iff_no_usedProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
deltaStar_pin_of_no_bad_used_profile_scanner
```

So a profile catalogue gives the universal incidence bound from two local absence certificates:

```text
no used profile has an invalid or beaten representative;
no used profile representative has bad-scalar count above B.
```

This is the plain-profile analogue of the refined-profile scanner route.  It still does not choose
the right profile or prove the count bound; it makes the certificate exact once such a profile is
proposed.

## Continuation: universal incidence iff after max scanner

The universal incidence layer now has direct exact iff wrappers once the profile-fiber max scanner
has passed:

```lean
worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_profileFiberMaxReps
not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_profileFiberMaxReps
worstCaseIncidenceBounded_iff_no_usedProfile_budget_lt_of_no_bad_used_profile
not_worstCaseIncidenceBounded_iff_exists_usedProfile_budget_lt_of_no_bad_used_profile
```

So after exact profile-fiber representatives are known, the original universal `WordStack` budget is
equivalent to a purely local used-profile budget scan:

```text
no used profile representative has bad-scalar count above B.
```

Conversely, a failed universal incidence bound is exactly one used profile label whose
representative is above `B`.  This sharpens the profile route's residual: the global quantifier is
gone only after the max-representative scanner is accepted; the remaining mathematical work is still
to produce a useful profile catalogue and prove its local budget.
