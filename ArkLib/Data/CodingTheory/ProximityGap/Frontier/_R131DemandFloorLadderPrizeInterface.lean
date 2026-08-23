/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R123DemandFloorDivFourInterface
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R128DemandFloorLadderMajorantPackage

/-!
# Prize-coordinate consumer for the ladder-list majorant route

R128 packages the remaining deep-tail theorem as uniform domination by production-field
ladder-list counts.  This file exposes that route directly in the `(r,n)` coordinate used by
the workbench, matching the KKH26 census interface in R130.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R131DemandFloorLadderPrizeInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface
open ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage

/-- Uniform closed prefixes plus ladder-list majorants give the divisibility-form demand
budget in the workbench `(r,n)` coordinate. -/
theorem demand_floor_of_dvd_four_prefixes_and_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_natural_demand_theorem Bad
    (ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.natural_demand_theorem_of_prefixes_and_ladder_majorants
      Bad hmajor hprefix)
    r n hn hg hr hrg

/-- Positive-rung version for callers that track the exclusions `r ≠ 0,1,2` rather than
the explicit inequality `3 ≤ r`. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_ladder_majorants
    (Bad : ℕ → ℕ → ℕ)
    (hmajor : HasLadderMajorants Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_of_dvd_four_natural_demand_theorem Bad
    (ArkLib.ProximityGap.Frontier.R128DemandFloorLadderMajorantPackage.natural_demand_theorem_of_prefixes_and_ladder_majorants
      Bad hmajor hprefix)
    r n hn hg hr0 hr1 hr2 hrg

/-- A single divisible-by-four budget overrun refutes the combined ladder-list route. -/
theorem not_prefixes_and_ladder_majorants_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasLadderMajorants Bad ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hmajor, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_ladder_majorants
      Bad hmajor hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R131DemandFloorLadderPrizeInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R131DemandFloorLadderPrizeInterface.demand_floor_of_dvd_four_prefixes_and_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R131DemandFloorLadderPrizeInterface.demand_floor_positive_of_dvd_four_prefixes_and_ladder_majorants
#print axioms
  ArkLib.ProximityGap.Frontier.R131DemandFloorLadderPrizeInterface.not_prefixes_and_ladder_majorants_of_dvd_four_budget_lt_bad
