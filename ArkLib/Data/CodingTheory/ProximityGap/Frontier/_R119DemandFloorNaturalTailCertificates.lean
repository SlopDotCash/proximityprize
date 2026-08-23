/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R118DemandFloorActiveRangeBridge

/-!
# Natural-range deep-tail orbit certificates

R116 defines deep-tail orbit certificates using the substrate active condition `2*r ≤ 2*g`.
R118 exposes consumers with the natural condition `r ≤ g`.  This file moves the certificate
predicate itself into that natural range.

The remaining open demand-side combinatorics can now target:

`∀ r, 6 ≤ r → r ≤ g → ∃ OP ≤ C(2g,r-1), Bad r (4g) ≤ (4g)*OP + 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R116DemandFloorOrbitTailReduction
open ArkLib.ProximityGap.Frontier.R118DemandFloorActiveRangeBridge

/-- Natural-range version of the deep-tail orbit certificate. -/
def HasDeepTailOrbitCertificatesLe (Bad : ℕ → ℕ → ℕ) (g : ℕ) : Prop :=
  ∀ r : ℕ, 6 ≤ r → r ≤ g →
    ∃ OP : ℕ, OP ≤ (2 * g).choose (r - 1) ∧ Bad r (4 * g) ≤ (4 * g) * OP + 1

/-- The natural-range certificate implies the substrate-style active certificate. -/
theorem active_certificates_of_le_certificates
    (Bad : ℕ → ℕ → ℕ) (g : ℕ)
    (htail : HasDeepTailOrbitCertificatesLe Bad g) :
    HasDeepTailOrbitCertificates Bad g := by
  intro r hr hactive
  have hrg : r ≤ g := by omega
  exact htail r hr hrg

/-- Natural-range certificates give the deep-tail budget bound. -/
theorem deep_tail_budget_of_le_certificates
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (htail : HasDeepTailOrbitCertificatesLe Bad g)
    (hr : 6 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact deep_tail_budget_of_orbit_certificates_le Bad g r
    (active_certificates_of_le_certificates Bad g htail) hr hrg

/-- Closed prefix plus natural-range deep-tail orbit certificates imply the demand budget for
every `3 ≤ r ≤ g`. -/
theorem demand_floor_r_ge_three_le_g_of_closed_prefix_and_le_certificates
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificatesLe Bad g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_r_ge_three_le_g_of_closed_prefix_and_tail_orbits
    Bad g r hg hprefix (active_certificates_of_le_certificates Bad g htail) hr hrg

/-- Positive-rung version driven by natural-range deep-tail orbit certificates. -/
theorem demand_floor_positive_rung_le_g_of_closed_prefix_and_le_certificates
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ g)
    (hprefix : AgreesWithClosedDemandPrefix Bad g)
    (htail : HasDeepTailOrbitCertificatesLe Bad g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_positive_rung_le_g_of_closed_prefix_and_tail_orbits
    Bad g r hg hr0 hr1 hr2 hrg hprefix
    (active_certificates_of_le_certificates Bad g htail)

/-- A budget overrun at `6 ≤ r ≤ g` refutes natural-range deep-tail certificates. -/
theorem not_le_certificates_of_deep_tail_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hr : 6 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ HasDeepTailOrbitCertificatesLe Bad g := by
  intro htail
  exact (Nat.not_le.mpr hgt)
    (deep_tail_budget_of_le_certificates Bad g r htail hr hrg)

end ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.HasDeepTailOrbitCertificatesLe
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.active_certificates_of_le_certificates
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.deep_tail_budget_of_le_certificates
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.demand_floor_r_ge_three_le_g_of_closed_prefix_and_le_certificates
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.demand_floor_positive_rung_le_g_of_closed_prefix_and_le_certificates
#print axioms
  ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates.not_le_certificates_of_deep_tail_budget_lt_bad
