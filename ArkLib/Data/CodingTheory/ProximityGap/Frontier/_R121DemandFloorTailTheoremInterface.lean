/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R120DemandFloorNaturalCertificatePackage

/-!
# Demand-tail theorem interface

R120 packages the remaining demand-side data at one active `g`: checked prefix agreement plus
natural-range deep-tail orbit certificates.  This file packages that target as a named theorem
family and records the exact consumer shape needed by later prize-facing work:

* prove the natural demand certificate at every active `g`;
* obtain the workbench demand budget for every active `3 ≤ r ≤ g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage

/-- The remaining natural-range demand theorem for a candidate bad-count family. -/
def NaturalDemandCertificateTheorem (Bad : ℕ → ℕ → ℕ) : Prop :=
  ∀ g : ℕ, 3 ≤ g → HasNaturalDemandCertificate Bad g

/-- The package implies the workbench demand budget for every active `3 ≤ r ≤ g`. -/
theorem demand_floor_active_of_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_r_ge_three_le_g_of_natural_demand_certificate
    Bad g r hg (hcerts g hg) hr hrg

/-- Positive-rung variant of the same package consumer. -/
theorem demand_floor_positive_active_of_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  have hr : 3 ≤ r := by omega
  exact demand_floor_active_of_natural_demand_theorem Bad hcerts g r hg hr hrg

/-- A single active budget overrun refutes the whole natural package. -/
theorem not_natural_demand_theorem_of_active_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ NaturalDemandCertificateTheorem Bad := by
  intro hcerts
  exact (Nat.not_le.mpr hgt)
    (demand_floor_active_of_natural_demand_theorem Bad hcerts g r hg hr hrg)

end ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface.NaturalDemandCertificateTheorem
#print axioms
  ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface.demand_floor_active_of_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface.demand_floor_positive_active_of_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface.not_natural_demand_theorem_of_active_budget_lt_bad
