/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R110DemandFloorClosedRungBudgetConsumers

/-!
# Closed r=4/r=5 counts in the general workbench budget

R110 identifies the named r=4 and r=5 budgets with the workbench's general
`deepBandBudgetR r n = 2^r * C(n/2,r)`.

This file exposes the already-proven r=4/r=5 deep-band count theorems directly in that general
budget language.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R110DemandFloorClosedRungBudgetConsumers

/-- The closed r=4 count satisfies the general workbench budget at `n = 4g`. -/
theorem deepBandBadCount4_le_deepBandBudgetR (g : ℕ) (hg : 2 ≤ g) :
    ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4 g ≤ deepBandBudgetR 4 (4 * g) := by
  rw [deepBandBudgetR_four_eq_deepBandBudget4]
  exact ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4_le_budget g hg

/-- The r=4 half-budget theorem in general workbench-budget form. -/
theorem two_mul_deepBandBadCount4_le_deepBandBudgetR (g : ℕ) (hg : 3 ≤ g) :
    2 * ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4 g ≤ deepBandBudgetR 4 (4 * g) := by
  rw [deepBandBudgetR_four_eq_deepBandBudget4]
  exact ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4_two_mul_le_budget g hg

/-- The closed r=5 count satisfies the general workbench budget at `n = 4g`. -/
theorem deepBandBadCount5_le_deepBandBudgetR (g : ℕ) (hg : 3 ≤ g) :
    ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5 g ≤ deepBandBudgetR 5 (4 * g) := by
  rw [deepBandBudgetR_five_eq_deepBandBudget5]
  exact ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5_le_budget g hg

/-- The r=5 half-budget theorem in general workbench-budget form. -/
theorem two_mul_deepBandBadCount5_le_deepBandBudgetR (g : ℕ) (hg : 3 ≤ g) :
    2 * ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5 g ≤ deepBandBudgetR 5 (4 * g) := by
  rw [deepBandBudgetR_five_eq_deepBandBudget5]
  exact ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5_two_mul_le_budget g hg

end ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget.deepBandBadCount4_le_deepBandBudgetR
#print axioms
  ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget.two_mul_deepBandBadCount4_le_deepBandBudgetR
#print axioms
  ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget.deepBandBadCount5_le_deepBandBudgetR
#print axioms
  ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget.two_mul_deepBandBadCount5_le_deepBandBudgetR
