/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R119DemandFloorNaturalTailCertificates

/-!
# Packaged natural demand certificate

R119 exposes the remaining demand-side tail in the clean range `6 ≤ r ≤ g`.  This file packages
the checked prefix agreement and that natural tail certificate into one predicate, then exposes
the workbench budget consumer and its matching obstruction.

Future combinatorial work can now aim to produce `HasNaturalDemandCertificate Bad g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates

/-- The natural demand-side certificate package: agreement with the checked r=3,4,5 prefix plus
deep-tail orbit certificates for every `6 ≤ r ≤ g`. -/
def HasNaturalDemandCertificate (Bad : ℕ → ℕ → ℕ) (g : ℕ) : Prop :=
  AgreesWithClosedDemandPrefix Bad g ∧ HasDeepTailOrbitCertificatesLe Bad g

/-- Extract the checked-prefix component of a natural demand certificate. -/
theorem prefix_of_natural_demand_certificate
    (Bad : ℕ → ℕ → ℕ) (g : ℕ)
    (hcert : HasNaturalDemandCertificate Bad g) :
    AgreesWithClosedDemandPrefix Bad g := by
  exact hcert.1

/-- Extract the natural deep-tail component of a natural demand certificate. -/
theorem tail_of_natural_demand_certificate
    (Bad : ℕ → ℕ → ℕ) (g : ℕ)
    (hcert : HasNaturalDemandCertificate Bad g) :
    HasDeepTailOrbitCertificatesLe Bad g := by
  exact hcert.2

/-- A natural demand certificate proves the workbench budget for every `3 ≤ r ≤ g`. -/
theorem demand_floor_r_ge_three_le_g_of_natural_demand_certificate
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hcert : HasNaturalDemandCertificate Bad g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_r_ge_three_le_g_of_closed_prefix_and_le_certificates
    Bad g r hg
    (prefix_of_natural_demand_certificate Bad g hcert)
    (tail_of_natural_demand_certificate Bad g hcert)
    hr hrg

/-- Positive-rung consumer for callers that track exclusions of `r = 0,1,2`. -/
theorem demand_floor_positive_rung_le_g_of_natural_demand_certificate
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hcert : HasNaturalDemandCertificate Bad g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤ deepBandBudgetR r (4 * g) := by
  exact demand_floor_positive_rung_le_g_of_closed_prefix_and_le_certificates
    Bad g r hg hr0 hr1 hr2 hrg
    (prefix_of_natural_demand_certificate Bad g hcert)
    (tail_of_natural_demand_certificate Bad g hcert)

/-- A budget overrun in the active demand range refutes the packaged natural certificate. -/
theorem not_natural_demand_certificate_of_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ) (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r (4 * g) < Bad r (4 * g)) :
    ¬ HasNaturalDemandCertificate Bad g := by
  intro hcert
  exact (Nat.not_le.mpr hgt)
    (demand_floor_r_ge_three_le_g_of_natural_demand_certificate
      Bad g r hg hcert hr hrg)

end ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.HasNaturalDemandCertificate
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.prefix_of_natural_demand_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.tail_of_natural_demand_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.demand_floor_r_ge_three_le_g_of_natural_demand_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.demand_floor_positive_rung_le_g_of_natural_demand_certificate
#print axioms
  ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage.not_natural_demand_certificate_of_budget_lt_bad
