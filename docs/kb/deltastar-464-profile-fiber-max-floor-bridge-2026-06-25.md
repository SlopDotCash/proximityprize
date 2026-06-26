# Issue #464: profile-fiber maxima feed the floor closure contract

Date: 2026-06-25.

Status: **composition bridge**, not a delta-star proof.

## What Was Added

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_ProfileFiberMaxFloorBridge.lean
```

connects two existing guardrails:

```text
_StackProfileFiberMax.lean
_FloorClosureContract.lean
```

The floor closure contract now wants a concrete max-containment certificate for the chosen finite
family.  The profile route wants to prove that a representative `rep p` is an exact bad-scalar
maximizer in every used profile fiber.

This bridge composes those statements: exact profile-fiber representatives give
`FamilyContainsGlobalMax` for the finite image of representatives, so they can feed the Linnik/TZ
floor contracts directly.

## New Sockets

The main positive bridges are:

```lean
floorFamilyContainsGlobalMax_of_profileFiberMaxReps
floorFamilyContainsGlobalMax_of_no_bad_used_profile
```

The first turns exact fiber-max representatives into:

```text
(Finset.univ.image rep) contains a true global bad-scalar maximizer.
```

The second consumes the scanner-positive certificate from `_StackProfileFiberMax.lean` directly:
if no used profile has an outside representative and no same-profile beating witness, then the
representative image contains a global maximizer.

The floor consumers are:

```lean
worstCaseIncidenceBounded_of_profileFiberMax_floorFamilyBounded
worstCaseIncidenceBounded_of_no_bad_used_profile_floorFamilyBounded
deltaStar_pin_of_linnik_candidateListExactSmallest_profileFiberMaxContract
deltaStar_pin_of_tz_candidateListExactSmallest_profileFiberMaxContract
```

So a profile classification can now feed the Linnik/TZ floor contracts without restating a
domination theorem.

## Refutation Socket

The negative bridge is:

```lean
not_floorFamilyContainsGlobalMax_of_each_profile_rep_beaten
```

If every profile representative in the finite image is beaten by some stack, then that image cannot
contain a global maximizer.  This is stronger than checking only used profiles, because the image is
taken over every `p : P`.

## Consequence

The profile/binder route now has a single honest final shape:

```text
exact singleton floor-bad scanner evidence
+ sub-prize least-prime supply
+ floor-goodness budgets the representative image
+ representatives are exact profile-fiber bad-scalar maxima
+ scaled MCA budget
=> delta-star lower pin
```

This does not prove the floor.  It removes an interface gap: a future scanner or classification
proof can target exact fiber maxima and feed the existing floor contract without restating the
global domination argument.
