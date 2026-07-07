/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R117DemandFloorTailObstructions

/-!
# Active-range wrappers for the demand-tail orbit interface

R116/R117 use the substrate-friendly active condition `2*r ≤ 2*g`.  In the `n = 4g` coordinate
this is just `r ≤ g`.  This file exposes the positive and obstruction reducers with that cleaner
side condition, so later orbit-count work can state its hypotheses in the natural rung range.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction
open ArkLib.ProximityGap.Frontier.R117DemandFloorTailObstructions

/-- In natural coordinates, the active range `2*r ≤ 2*g` is implied by `r ≤ g`. -/
theorem active_range_of_le (r g : ℕ) (hrg : r ≤ g) : 2 * r ≤ 2 * g := by
  omega

/-- Deep-tail orbit certificates give the budget bound in the natural active range `r ≤ g`. -/
theorem deep_tail_budget_of_orbit_certificates_le
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (htail : HasDeepTailOrbitCertificates Bad g)
    (hr : 6 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact deep_tail_budget_of_orbit_certificates Bad g r htail hr
    (active_range_of_le r g hrg)

/-- Closed prefix plus deep-tail orbit certificates imply the demand budget for every
`3 ≤ r ≤ g` in the `n = 4g` coordinate. -/
theorem demand_floor_r_ge_three_le_g_of_closed_prefix_and_tail_orbits
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificates Bad g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_active_r_ge_three_of_closed_prefix_and_tail_orbits
    Bad g r hg hprefix htail hr (active_range_of_le r g hrg)

/-- Positive-rung version with the natural active range `r ≤ g`. -/
theorem demand_floor_positive_rung_le_g_of_closed_prefix_and_tail_orbits
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificates Bad g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_active_positive_rung_of_closed_prefix_and_tail_orbits
    Bad g r hg hr0 hr1 hr2 (active_range_of_le r g hrg) hprefix htail

/-- A budget overrun at a natural-range deep rung refutes the deep-tail certificates. -/
theorem not_deep_tail_orbit_certificates_of_budget_lt_bad_le
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hr : 6 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ HasDeepTailOrbitCertificates Bad g := by
  exact not_deep_tail_orbit_certificates_of_budget_lt_bad
    Bad g r hr (active_range_of_le r g hrg) hgt

/-- A budget overrun at any `3 ≤ r ≤ g` refutes the full closed-prefix-plus-tail package. -/
theorem not_closed_prefix_and_tail_orbits_of_budget_lt_bad_le
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ (AgreesWithClosedDemandPrefix Bad g ∧ HasDeepTailOrbitCertificates Bad g) := by
  exact not_closed_prefix_and_tail_orbits_of_budget_lt_bad
    Bad g r hg hr (active_range_of_le r g hrg) hgt

end ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.active_range_of_le
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.deep_tail_budget_of_orbit_certificates_le
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.demand_floor_r_ge_three_le_g_of_closed_prefix_and_tail_orbits
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.demand_floor_positive_rung_le_g_of_closed_prefix_and_tail_orbits
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.not_deep_tail_orbit_certificates_of_budget_lt_bad_le
#print axioms
  ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge.not_closed_prefix_and_tail_orbits_of_budget_lt_bad_le
