/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R122DemandFloorNCoordinateInterface

/-!
# Divisibility-form n-coordinate interface

R122 consumes an explicit witness `n = 4*g`.  In downstream statements the same data often
appears as `4 ∣ n` and the natural coordinate `g = n/4`.  This file packages that rewrite once.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R121DemandFloorTailTheoremInterface
open ArkLib.ProximityGap.Frontier.R122DemandFloorNCoordinateInterface

/-- If `4 ∣ n`, then `n = 4 * (n / 4)`. -/
theorem eq_four_mul_div_four_of_dvd (n : ℕ) (hn : 4 ∣ n) :
    n = 4 * (n / 4) := by
  rcases hn with ⟨g, rfl⟩
  omega

/-- Divisibility-form consumer for the universal natural demand theorem. -/
theorem demand_floor_of_dvd_four_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_n_of_natural_demand_theorem
    Bad hcerts r n (n / 4) (eq_four_mul_div_four_of_dvd n hn) hg hr hrg

/-- Positive-rung divisibility-form consumer. -/
theorem demand_floor_positive_of_dvd_four_natural_demand_theorem
    (Bad : ℕ → ℕ → ℕ)
    (hcerts : NaturalDemandCertificateTheorem Bad)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr0 : r ≠ 0)
    (hr1 : r ≠ 1)
    (hr2 : r ≠ 2)
    (hrg : r ≤ n / 4) :
    Bad r n ≤ deepBandBudgetR r n := by
  exact demand_floor_positive_n_of_natural_demand_theorem
    Bad hcerts r n (n / 4) (eq_four_mul_div_four_of_dvd n hn) hg hr0 hr1 hr2 hrg

/-- A divisibility-form budget overrun refutes the universal natural demand theorem. -/
theorem not_natural_demand_theorem_of_dvd_four_budget_lt_bad
    (Bad : ℕ → ℕ → ℕ)
    (r n : ℕ)
    (hn : 4 ∣ n)
    (hg : 3 ≤ n / 4)
    (hr : 3 ≤ r)
    (hrg : r ≤ n / 4)
    (hgt : deepBandBudgetR r n < Bad r n) :
    ¬ NaturalDemandCertificateTheorem Bad := by
  exact not_natural_demand_theorem_of_n_budget_lt_bad
    Bad r n (n / 4) (eq_four_mul_div_four_of_dvd n hn) hg hr hrg hgt

end ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface.eq_four_mul_div_four_of_dvd
#print axioms
  ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface.demand_floor_of_dvd_four_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface.demand_floor_positive_of_dvd_four_natural_demand_theorem
#print axioms
  ArkLib.ProximityGap.Frontier.R123DemandFloorDivFourInterface.not_natural_demand_theorem_of_dvd_four_budget_lt_bad
