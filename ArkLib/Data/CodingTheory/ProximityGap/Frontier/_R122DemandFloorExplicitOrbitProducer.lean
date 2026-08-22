/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R121DemandFloorTailTheoremInterface

/-!
# Explicit orbit-count producer for the demand tail

R121 states the remaining demand-side goal as a theorem family producing packaged natural
certificates.  This file lowers that target to an explicit orbit-count function:

`OP g r ≤ C(2g, r-1)` and `Bad r (4g) ≤ (4g) * OP g r + 1`

for every active tail rung `6 ≤ r ≤ g`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer

open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R119DemandFloorNaturalTailCertificates
open ArkLib.ProximityGap.Frontier.R120DemandFloorNaturalCertificatePackage
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface

/-- An explicit orbit-count function satisfies the natural tail certificate obligations. -/
def ExplicitNaturalTailOrbitProducer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ) : Prop :=
  ∀ g r : ℕ, 3 ≤ g → 6 ≤ r → r ≤ g →
    OP g r ≤ (2 * g).choose (r - 1) ∧ Bad r (4 * g) ≤ (4 * g) * OP g r + 1

/-- An explicit producer gives the R119 natural tail certificates at one `g`. -/
theorem le_certificates_of_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP)
    (g : ℕ) (hg : 3 ≤ g) :
    HasDeepTailOrbitCertificatesLe Bad g := by
  intro r hr hrg
  rcases hOP g r hg hr hrg with ⟨hbound, hbad⟩
  exact ⟨OP g r, hbound, hbad⟩

/-- Prefix agreement plus an explicit orbit producer gives the per-`g` natural demand
certificate. -/
theorem natural_demand_certificate_of_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP)
    (g : ℕ) (hg : 3 ≤ g) :
    HasNaturalDemandCertificate Bad g := by
  exact ⟨hprefix g hg, le_certificates_of_explicit_orbit_producer Bad OP hOP g hg⟩

/-- Prefix agreement plus an explicit orbit producer gives the uniform R121 theorem family. -/
theorem natural_demand_theorem_of_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP) :
    NaturalDemandCertificateTheorem Bad := by
  intro g hg
  exact natural_demand_certificate_of_explicit_orbit_producer Bad OP hprefix hOP g hg

/-- Direct budget consumer from an explicit orbit producer. -/
theorem demand_floor_active_of_explicit_orbit_producer
    (Bad : ℕ → ℕ → ℕ) (OP : ℕ → ℕ → ℕ)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (hOP : ExplicitNaturalTailOrbitProducer Bad OP)
    (g r : ℕ)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r (4 * g) ≤
      ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge.deepBandBudgetR r (4 * g) := by
  exact demand_floor_active_of_natural_demand_theorem Bad
    (natural_demand_theorem_of_explicit_orbit_producer Bad OP hprefix hOP)
    g r hg hr hrg

end ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer.ExplicitNaturalTailOrbitProducer
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer.le_certificates_of_explicit_orbit_producer
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer.natural_demand_certificate_of_explicit_orbit_producer
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer.natural_demand_theorem_of_explicit_orbit_producer
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorExplicitOrbitProducer.demand_floor_active_of_explicit_orbit_producer
