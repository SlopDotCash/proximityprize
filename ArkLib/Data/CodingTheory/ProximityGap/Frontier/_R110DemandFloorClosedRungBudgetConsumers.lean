/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR4Bound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR5Bound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R109DemandFloorGeneralBudgetBridge

/-!
# Closed-rung consumers for the general demand-side orbit bridge

R109 packages the demand-side orbit-count bridge in the general workbench budget
`deepBandBudgetR r n = 2^r * C(n/2,r)`.

This file specializes that bridge to the named r=4 and r=5 budget definitions already used by the
closed deep-band rung files.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge

/-- The general workbench budget at `r = 4`, `n = 4g`, is the named r=4 budget. -/
theorem deepBandBudgetR_four_eq_deepBandBudget4 (g : ℕ) :
    deepBandBudgetR 4 (4 * g) = ArkLib.ProximityGap.DeepBandR4.deepBandBudget4 g := by
  rw [deepBandBudgetR_four_mul]
  rfl

/-- The general workbench budget at `r = 5`, `n = 4g`, is the named r=5 budget. -/
theorem deepBandBudgetR_five_eq_deepBandBudget5 (g : ℕ) :
    deepBandBudgetR 5 (4 * g) = ArkLib.ProximityGap.DeepBandR5.deepBandBudget5 g := by
  rw [deepBandBudgetR_four_mul]
  rfl

/-- r=4 closed-budget consumer: an honest orbit identity plus the orbit-count bound gives the
named r=4 demand-side budget. -/
theorem demand_floor_r4_budget_of_orbit_bound_plus_one
    (g OP bad : ℕ)
    (hg : 4 ≤ g)
    (hOP : OP ≤ (2 * g).choose 3)
    (hbad : bad ≤ (4 * g) * OP + 1) :
    bad ≤ ArkLib.ProximityGap.DeepBandR4.deepBandBudget4 g := by
  rw [← deepBandBudgetR_four_eq_deepBandBudget4]
  exact demand_floor_four_mul_budget_of_orbit_bound_plus_one
    4 g OP bad (by norm_num) (by omega) hOP hbad

/-- r=4 closed-budget consumer without the possible zero orbit. -/
theorem demand_floor_r4_budget_of_orbit_bound
    (g OP bad : ℕ)
    (hg : 4 ≤ g)
    (hOP : OP ≤ (2 * g).choose 3)
    (hbad : bad ≤ (4 * g) * OP) :
    bad ≤ ArkLib.ProximityGap.DeepBandR4.deepBandBudget4 g :=
  demand_floor_r4_budget_of_orbit_bound_plus_one g OP bad hg hOP (by omega)

/-- r=5 closed-budget consumer: an honest orbit identity plus the orbit-count bound gives the
named r=5 demand-side budget. -/
theorem demand_floor_r5_budget_of_orbit_bound_plus_one
    (g OP bad : ℕ)
    (hg : 5 ≤ g)
    (hOP : OP ≤ (2 * g).choose 4)
    (hbad : bad ≤ (4 * g) * OP + 1) :
    bad ≤ ArkLib.ProximityGap.DeepBandR5.deepBandBudget5 g := by
  rw [← deepBandBudgetR_five_eq_deepBandBudget5]
  exact demand_floor_four_mul_budget_of_orbit_bound_plus_one
    5 g OP bad (by norm_num) (by omega) hOP hbad

/-- r=5 closed-budget consumer without the possible zero orbit. -/
theorem demand_floor_r5_budget_of_orbit_bound
    (g OP bad : ℕ)
    (hg : 5 ≤ g)
    (hOP : OP ≤ (2 * g).choose 4)
    (hbad : bad ≤ (4 * g) * OP) :
    bad ≤ ArkLib.ProximityGap.DeepBandR5.deepBandBudget5 g :=
  demand_floor_r5_budget_of_orbit_bound_plus_one g OP bad hg hOP (by omega)

end ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.deepBandBudgetR_four_eq_deepBandBudget4
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.deepBandBudgetR_five_eq_deepBandBudget5
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.demand_floor_r4_budget_of_orbit_bound_plus_one
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.demand_floor_r4_budget_of_orbit_bound
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.demand_floor_r5_budget_of_orbit_bound_plus_one
#print axioms
  ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers.demand_floor_r5_budget_of_orbit_bound
