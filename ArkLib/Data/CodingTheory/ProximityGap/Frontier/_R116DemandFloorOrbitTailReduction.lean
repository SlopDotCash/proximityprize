/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R115DemandFloorTailReduction

/-!
# Orbit-certificate tail reduction for the general-r demand budget

R109 proves that an orbit-count certificate plus the honest zero-orbit identity implies the
workbench budget.  R115 proves that, after the checked r=3,4,5 prefix, only the `r ≥ 6` tail
remains.

This file welds those two interfaces together: a future proof can target orbit certificates only
on the deep tail, and the closed prefix is discharged automatically.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction

/-- A tail orbit certificate in the `n = 4g` coordinate: for each deep rung in the active
range, there is an orbit count bounded by `C(2g,r-1)` and the bad count is bounded by the
honest zero-orbit expression `(4g) * OP + 1`. -/
def HasDeepTailOrbitCertificates (Bad : ℕ → ℕ → ℕ) (g : ℕ) : Prop :=
  ∀ s : ℕ, 6 ≤ s → 2 * s ≤ 2 * g →
    ∃ OP : ℕ, OP ≤ (2 * g).choose (s - 1) ∧ Bad s (4 * g) ≤ (4 * g) * OP + 1

/-- A deep-tail orbit certificate gives the deep-tail budget inequality. -/
theorem deep_tail_budget_of_orbit_certificates
    (Bad : ℕ → ℕ → ℕ) (g s : ℕ)
    (htail : HasDeepTailOrbitCertificates Bad g)
    (hs : 6 ≤ s)
    (hactive : 2 * s ≤ 2 * g) :
    Bad s (4 * g) ≤ deepBandBudgetR s (4 * g) := by
  rcases htail s hs hactive with ⟨OP, hOP, hbad⟩
  exact demand_floor_four_mul_budget_of_orbit_bound_plus_one
    s g OP (Bad s (4 * g)) (by omega) hactive hOP hbad

/-- Closed prefix plus deep-tail orbit certificates imply the workbench demand budget for every
active rung `r ≥ 3` in the `n = 4g` coordinate. -/
theorem demand_floor_active_r_ge_three_of_closed_prefix_and_tail_orbits
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificates Bad g)
    (hr : 3 ≤ r)
    (hactive : 2 * r ≤ 2 * g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  rcases hprefix with ⟨h3, h4, h5⟩
  have hclosed := closed_prefix_r3_r4_r5_deepBandBudgetR g hg
  rcases hclosed with ⟨hr3, hr4, hr5⟩
  rcases lt_or_ge r 6 with hlt | hge
  · interval_cases r <;> simpa [h3, h4, h5]
  · exact deep_tail_budget_of_orbit_certificates Bad g r htail hge hactive

/-- In the active range, the positive-rung variant from R115 can also be driven directly by
deep-tail orbit certificates. -/
theorem demand_floor_active_positive_rung_of_closed_prefix_and_tail_orbits
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hactive : 2 * r ≤ 2 * g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificates Bad g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  have hr : 3 ≤ r := by omega
  exact demand_floor_active_r_ge_three_of_closed_prefix_and_tail_orbits
    Bad g r hg hprefix htail hr hactive

end ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction.HasDeepTailOrbitCertificates
#print axioms
  ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction.deep_tail_budget_of_orbit_certificates
#print axioms
  ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction.demand_floor_active_r_ge_three_of_closed_prefix_and_tail_orbits
#print axioms
  ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction.demand_floor_active_positive_rung_of_closed_prefix_and_tail_orbits
