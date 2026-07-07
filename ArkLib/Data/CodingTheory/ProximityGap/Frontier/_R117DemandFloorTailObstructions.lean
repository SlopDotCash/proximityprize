/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R116DemandFloorOrbitTailReduction

/-!
# Obstructions to deep-tail demand orbit certificates

R116 gives a positive reducer: closed prefix plus active deep-tail orbit certificates imply the
workbench demand budget.  This file records the corresponding audit-facing contrapositives.

If a computed candidate bad-count family exceeds the budget at an active deep rung, then the
deep-tail orbit-certificate package cannot be present.  If it exceeds the budget at any active
`r ≥ 3` rung, then the full closed-prefix-plus-tail package cannot be present.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction

/-- A budget overrun at an active deep rung refutes the deep-tail orbit-certificate package. -/
theorem not_deep_tail_orbit_certificates_of_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hr : 6 ≤ r)
    (hactive : 2 * r ≤ 2 * g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ HasDeepTailOrbitCertificates Bad g := by
  intro htail
  exact (Nat.not_le.mpr hgt)
    (deep_tail_budget_of_orbit_certificates Bad g r htail hr hactive)

/-- A budget overrun at any active `r ≥ 3` rung refutes simultaneous agreement with the checked
prefix and deep-tail orbit certificates. -/
theorem not_closed_prefix_and_tail_orbits_of_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hactive : 2 * r ≤ 2 * g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ (AgreesWithClosedDemandPrefix Bad g ∧ HasDeepTailOrbitCertificates Bad g) := by
  rintro ⟨hprefix, htail⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_active_r_ge_three_of_closed_prefix_and_tail_orbits
      Bad g r hg hprefix htail hr hactive)

/-- Positive-rung version of the same obstruction, useful when the caller tracks exclusions of
`r = 0,1,2` rather than a direct `3 ≤ r` hypothesis. -/
theorem not_positive_closed_prefix_and_tail_orbits_of_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hactive : 2 * r ≤ 2 * g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ (AgreesWithClosedDemandPrefix Bad g ∧ HasDeepTailOrbitCertificates Bad g) := by
  have hr : 3 ≤ r := by omega
  exact not_closed_prefix_and_tail_orbits_of_budget_lt_bad
    Bad g r hg hr hactive hgt

end ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions.not_deep_tail_orbit_certificates_of_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions.not_closed_prefix_and_tail_orbits_of_budget_lt_bad
#print axioms
  ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions.not_positive_closed_prefix_and_tail_orbits_of_budget_lt_bad
