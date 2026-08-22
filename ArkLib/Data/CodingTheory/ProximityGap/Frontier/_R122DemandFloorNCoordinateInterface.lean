/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R121DemandFloorTailTheoremInterface

/-!
# n-coordinate interface for the natural demand theorem

R121 consumes the universal natural demand certificate in the `n = 4g` coordinate used by the
closed rungs.  The workbench conjecture is stated in `(r,n)` coordinates.  This file records the
thin bridge: whenever `n = 4g`, the R121 budget theorem rewrites directly to `Bad r n ≤
deepBandBudgetR r n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface

/-- The universal natural demand theorem gives the workbench budget in `(r,n)` coordinates for
every active witness `n = 4g`. -/
theorem demand_floor_n_of_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (r n g : ℕ)
    (hn : n = 4 * g)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g) :
    Bad r n ≤ deepBandBudgetR r n := by
  subst n
  exact demand_floor_active_of_natural_demand_theorem Bad hcerts g r hg hr hrg

/-- Positive-rung `(r,n)` version for callers that track exclusions of `r = 0,1,2`. -/
theorem demand_floor_positive_n_of_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (r n g : ℕ)
    (hn : n = 4 * g)
    (hg : 3 ≤ g)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ g) :
    Bad r n ≤ deepBandBudgetR r n := by
  subst n
  exact demand_floor_positive_active_of_natural_demand_theorem
    Bad hcerts g r hg hr0 hr1 hr2 hrg

/-- A budget overrun in `(r,n)` coordinates refutes the universal natural demand theorem. -/
theorem not_natural_demand_theorem_of_n_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n g : ℕ)
    (hn : n = 4 * g)
    (hg : 3 ≤ g)
    (hr : 3 ≤ r)
    (hrg : r ≤ g)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ NaturalDemandCertificateTheorem Bad := by
  subst n
  exact not_natural_demand_theorem_of_active_budget_lt_bad Bad g r hg hr hrg hgt

end ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface.demand_floor_n_of_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface.demand_floor_positive_n_of_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface.not_natural_demand_theorem_of_n_budget_lt_bad
