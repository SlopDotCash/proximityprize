# Issue #464: refined-profile scanners feed the floor contract

Date: 2026-06-26.

Status: **composition bridge**, not a delta-star proof.

## What Was Added

The frontier file

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_RefinedProfileFloorBridge.lean
```

connects the refined-profile scanner API to the floor closure contract.

The refinement route now has exact local certificates in
`_StackProfileRefinement.lean`:

```lean
fineFiberMaxReps_iff_no_bad_used_fineProfile
refinedProfileMaxesBounded_iff_no_usedFineProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_fineProfile_scanner
deltaStar_pin_of_no_bad_fineProfile_scanner
```

The floor route consumes a finite family only when it contains a true global bad-scalar maximizer.
The new bridge composes those requirements.

## New Sockets

The used fine-profile family is named:

```lean
usedFineProfileFinset
usedFineProfileRepFamily
```

It is the sharper family:

```text
{ rep q | q is actually attained by some stack }.
```

The main positive bridges are:

```lean
floorFamilyContainsGlobalMax_of_fineFiberMaxReps
floorFamilyContainsGlobalMax_of_fineFiberMaxReps_usedFineProfileFamily
floorFamilyContainsGlobalMax_of_no_bad_fineProfile
floorFamilyContainsGlobalMax_of_no_bad_fineProfile_usedFineProfileFamily
```

So a scanner certificate saying there is no invalid or beaten fine-profile representative can now
be passed directly into `FamilyContainsGlobalMax`.

The budget scanner is also packaged:

```lean
familyBounded_of_no_usedFineProfile_budget_lt
familyBounded_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt
floorGoodFamilyBudget_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_fineProfile_budgetScanner
deltaStar_pin_of_refinedScannerBudget
```

This is the fully local form: the used fine-profile representative family is bounded iff no used
representative is above budget.  Together with no bad fine-profile representative and the scaled MCA
budget, this implies the delta-star lower pin.

The Linnik/TZ floor consumers are:

```lean
familyBounded_of_no_usedFineProfile_budget_lt
worstCaseIncidenceBounded_of_no_bad_fineProfile_budgetScanner
deltaStar_pin_of_refinedScannerBudget
deltaStar_pin_of_linnik_candidateListExactSmallest_refinedProfileContract
deltaStar_pin_of_linnik_candidateListExactSmallest_refinedScannerContract
deltaStar_pin_of_linnik_candidateListExactSmallest_refinedBudgetScannerContract
deltaStar_pin_of_refinedBudgetScanner_of_linnikInputs
deltaStar_pin_of_tz_candidateListExactSmallest_refinedProfileContract
deltaStar_pin_of_tz_candidateListExactSmallest_refinedScannerContract
deltaStar_pin_of_tz_candidateListExactSmallest_refinedBudgetScannerContract
deltaStar_pin_of_refinedBudgetScanner_of_tzInputs
```

The first three sockets are the direct local scanner route: absence of a beaten representative plus
absence of an above-budget used representative gives `WorstCaseIncidenceBounded`, then the standard
delta-star pin.  In the substrate this is now
`StackProfileRefinement.deltaStar_pin_of_no_bad_fineProfile_scanner`; the bridge-level
`deltaStar_pin_of_refinedScannerBudget` is just the constant-coarse specialization.  The Linnik/TZ
sockets either consume `FloorGoodFamilyBudget` for
`usedFineProfileRepFamily fine rep` directly or derive that budget from the local no-above-budget
scanner certificate.

Diagnostic: `floorGoodFamilyBudget_of_no_usedFineProfile_budget_lt` is intentionally tautological.
If the scanner already controls actual bad-scalar counts for all used representatives, then
floor-goodness is not doing the counting work.  A genuinely off-BGK closure still needs a separate
theorem that floor-goodness itself budgets the chosen representative family when direct count
control is unavailable.
The exact iff `floorGoodFamilyBudget_usedFineProfileRepFamily_iff_no_usedFineProfile_budget_lt`
isolates that remaining burden under the floor-good premise.

The two `*_of_linnikInputs` / `*_of_tzInputs` theorems are the no-laundering guardrails: once the
direct refined scanner proves max-containment and budget, the same delta-star pin follows without
using the least-prime or TZ inputs.  Those analytic inputs can remove floor-localization
obstructions, but they do not supply the worst-stack counting bound unless a separate family-budget
theorem is proved.

## Refutation Socket

The local negative bridge is:

```lean
not_floorFamilyContainsGlobalMax_of_each_used_fineProfile_rep_beaten
not_floorFamilyContainsGlobalMax_usedFineProfileFamily_iff_each_used_rep_beaten
```

Failure of max-containment for the used representative family is now exactly the ability to beat
every used fine-profile representative.  This is the scanner refutation surface for any proposed
refined catalogue.

## Critical Verdict

This turns an iterative classification search into a precise floor-facing certificate:

```text
exact singleton floor-bad scanner evidence
+ sub-prize least-prime supply
+ floor-goodness budgets usedFineProfileRepFamily
+ no used fine profile has an invalid or beaten representative
+ no used fine-profile representative exceeds the scaled budget
+ scaled MCA budget
=> delta-star lower pin
```

The hard theorem is still the scanner/math certificate that the chosen fine profile has true fiber
maximizers within budget.  The bridge now removes both API gaps: max-containment and family
boundedness for the used fine-profile representative family.
