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
floor contracts directly.  The sharper scanner-facing family is
`usedProfileRepFamily profile rep`, the image of representatives only over profiles that are
actually attained by some stack.

## New Sockets

The used-profile family is now named explicitly:

```lean
usedProfileFinset
usedProfileRepFamily
```

It denotes:

```text
{ rep p | p is actually attained by some stack }.
```

The main positive bridges are:

```lean
floorFamilyContainsGlobalMax_of_profileFiberMaxReps
floorFamilyContainsGlobalMax_of_no_bad_used_profile
floorFamilyContainsGlobalMax_of_profileFiberMaxReps_usedProfileFamily
floorFamilyContainsGlobalMax_of_no_bad_used_profile_usedProfileFamily
```

The first turns exact fiber-max representatives into:

```text
(Finset.univ.image rep) contains a true global bad-scalar maximizer.
```

The used-profile variants target `usedProfileRepFamily profile rep`, so budgets and refutations
only quantify over representatives of profiles that occur.

The second consumes the scanner-positive certificate from `_StackProfileFiberMax.lean` directly:
if no used profile has an outside representative and no same-profile beating witness, then the
representative image contains a global maximizer.

The floor consumers are:

```lean
familyBounded_of_no_usedProfile_budget_lt
familyBounded_usedProfileRepFamily_iff_no_usedProfile_budget_lt
floorGoodFamilyBudget_of_no_usedProfile_budget_lt
floorGoodFamilyBudget_usedProfileRepFamily_iff_no_usedProfile_budget_lt
worstCaseIncidenceBounded_of_profileFiberMax_floorFamilyBounded
worstCaseIncidenceBounded_of_no_bad_used_profile_floorFamilyBounded
worstCaseIncidenceBounded_of_profileFiberMax_usedProfileFloorFamilyBounded
worstCaseIncidenceBounded_of_no_bad_used_profile_usedProfileFloorFamilyBounded
worstCaseIncidenceBounded_of_no_bad_used_profile_budgetScanner
deltaStar_pin_of_profileScannerBudget
deltaStar_pin_of_linnik_candidateListExactSmallest_profileFiberMaxContract
deltaStar_pin_of_tz_candidateListExactSmallest_profileFiberMaxContract
deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileFiberMaxContract
deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileFiberMaxContract
deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileScannerContract
deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileScannerContract
deltaStar_pin_of_linnik_candidateListExactSmallest_usedProfileBudgetScannerContract
deltaStar_pin_of_profileBudgetScanner_of_linnikInputs
deltaStar_pin_of_tz_candidateListExactSmallest_usedProfileBudgetScannerContract
deltaStar_pin_of_profileBudgetScanner_of_tzInputs
```

So a profile classification can now feed the Linnik/TZ floor contracts without restating a
domination theorem.

The budget scanner is exact for the used-profile family: the family is bounded iff no used
representative is above budget.  The `floorGoodFamilyBudget_of_no_usedProfile_budget_lt` bridge is
diagnostic.  If a scanner already controls actual bad-scalar counts for all used representatives,
then floor-goodness is not doing the counting work; a genuinely off-BGK closure still needs a
separate theorem that floor-goodness itself budgets the chosen representatives.
The exact iff `floorGoodFamilyBudget_usedProfileRepFamily_iff_no_usedProfile_budget_lt` isolates
that remaining burden under the floor-good premise.

The two `*_of_linnikInputs` / `*_of_tzInputs` wrappers make that diagnostic explicit: once the
profile scanner already proves max-containment and the used-profile budget, the same delta-star pin
follows without using the least-prime or TZ supply hypotheses as counting input.

The substrate now exposes the same budget scanner directly, before passing through the floor
contract:

```lean
not_profileFiberMaxesBounded_iff_exists_usedProfile_budget_lt
profileFiberMaxesBounded_iff_no_usedProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_used_profile_scanner
deltaStar_pin_of_no_bad_used_profile_scanner
```

This matters for attack hygiene.  The exact profile scanner has two independent obligations:

```text
no used representative is invalid or beaten inside its own profile
no used representative exceeds the MCA bad-scalar budget
```

Together they already imply `WorstCaseIncidenceBounded`.  Therefore a proposed floor-localization
argument is genuinely off-BGK only if it proves a family-budget theorem from floor-goodness without
assuming this second scanner obligation.  Otherwise the proof has simply restated the original
worst-stack bound in profile language.

Local PDF sweep check: the Paley-spectrum reference library still supports this verdict.  The
generalized-Paley papers identify the Gauss-period spectral dictionary; HBK/Stepanov applies above
the prize thinness; BGK/Bourgain-Chang/Kowalski gives nontrivial but ineffective thin-subgroup
cancellation of the form `n * p^{-nu(gamma)}`, not the required `sqrt(n log(p/n))`.  So the profile
scanner budget is not supplied by any currently collected analytic reference; it is exactly the
on-BGK counting theorem unless an independent floor-good family-budget theorem is found.

## Refutation Socket

The negative bridge is:

```lean
not_floorFamilyContainsGlobalMax_of_each_profile_rep_beaten
not_floorFamilyContainsGlobalMax_of_each_used_profile_rep_beaten
not_floorFamilyContainsGlobalMax_usedProfileFamily_iff_each_used_rep_beaten
```

If every profile representative in the finite image is beaten by some stack, then that image cannot
contain a global maximizer.  This is stronger than checking only used profiles, because the image is
taken over every `p : P`.

The used-profile refutation is the sharper scanner socket: it only requires a beating witness for
each actually used representative.

## Consequence

The profile/binder route now has a single honest final shape:

```text
exact singleton floor-bad scanner evidence
+ sub-prize least-prime supply
+ floor-goodness budgets the representative image, preferably usedProfileRepFamily
+ representatives are exact profile-fiber bad-scalar maxima
+ scaled MCA budget
=> delta-star lower pin
```

This does not prove the floor.  It removes an interface gap: a future scanner or classification
proof can target exact fiber maxima and feed the existing floor contract with either the full image
or the tighter used-profile family, without restating the global domination argument.
