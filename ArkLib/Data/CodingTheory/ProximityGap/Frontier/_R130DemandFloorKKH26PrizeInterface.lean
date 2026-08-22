/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R123DemandFloorDivFourInterface
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R129DemandFloorKKH26CensusPackage

/-!
# Prize-coordinate consumer for the KKH26 census route

R129 packages the remaining deep-tail theorem as uniform domination by exact KKH26
monomial-pair censuses.  This file exposes the route directly in the `(r,n)` coordinate used by
the workbench: once the closed `r = 3,4,5` prefix is known and the deep tail is KKH26-census
dominated, every active divisible-by-four rung satisfies the demand budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R130DemandFloorKKH26PrizeInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R115DemandFloorTailReduction
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface
open ArkLib.ProximityGap.Frontier.R129DemandFloorKKH26CensusPackage

/-- Uniform closed prefixes plus KKH26 census domination give the divisibility-form demand
budget in the workbench `(r,n)` coordinate. -/
theorem demand_floor_of_dvd_four_prefixes_and_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad)
    (hprefix : ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_of_dvd_four_natural_demand_theorem Bad
    (natural_demand_theorem_of_prefixes_and_kkh26_census_dominators Bad hdom hprefix)
    r n hn hg hr hrg

/-- Positive-rung version for callers that track the exclusions `r ≠ 0,1,2` rather than
the explicit inequality `3 ≤ r`. -/
theorem demand_floor_positive_of_dvd_four_prefixes_and_kkh26_census_dominators
    (Bad : ℕ → ℕ → ℕ)
    (hdom : HasKKH26CensusDominators Bad)
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
    (natural_demand_theorem_of_prefixes_and_kkh26_census_dominators Bad hdom hprefix)
    r n hn hg hr0 hr1 hr2 hrg

/-- A single divisible-by-four budget overrun refutes the combined KKH26 census route. -/
theorem not_prefixes_and_kkh26_census_dominators_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ (HasKKH26CensusDominators Bad ∧
      ∀ g : ℕ, 3 ≤ g → AgreesWithClosedDemandPrefix Bad g) := by
  rintro ⟨hdom, hprefix⟩
  exact (Nat.not_le.mpr hgt)
    (demand_floor_of_dvd_four_prefixes_and_kkh26_census_dominators
      Bad hdom hprefix r n hn hg hr hrg)

end ArkLib.ProximityGap.Frontier.R130DemandFloorKKH26PrizeInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R130DemandFloorKKH26PrizeInterface.demand_floor_of_dvd_four_prefixes_and_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R130DemandFloorKKH26PrizeInterface.demand_floor_positive_of_dvd_four_prefixes_and_kkh26_census_dominators
#print axioms
  ArkLib.ProximityGap.Frontier.R130DemandFloorKKH26PrizeInterface.not_prefixes_and_kkh26_census_dominators_of_dvd_four_budget_lt_bad
