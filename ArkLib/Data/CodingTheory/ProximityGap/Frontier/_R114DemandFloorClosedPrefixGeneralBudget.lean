/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R112DemandFloorClosedRungGeneralBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R113DemandFloorR3GeneralBudget

/-!
# Closed prefix of the general deep-band demand budget

The workbench asks for a general-r theorem of the shape

`deepBandBadCount_r r n ≤ deepBandBudgetR r n`.

R113 and R112 expose the proven r=3,4,5 instances in this budget language.  This file packages
that checked prefix as one consumer, so later general-r work can target the first genuinely open
rung without re-opening the closed base cases.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge
open ArkLib.ProximityGap.Frontier.R112DemandFloorClosedRungGeneralBudget
open ArkLib.ProximityGap.Frontier.R113DemandFloorR3GeneralBudget

/-- The proven closed prefix `r = 3,4,5` of the workbench general-r demand budget. -/
theorem closed_prefix_r3_r4_r5_deepBandBudgetR (g : ℕ) (hg : 3 ≤ g) :
    ArkLib.ProximityGap.DeepBandR3.deepBandBadCount g ≤ deepBandBudgetR 3 (4 * g) ∧
      ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4 g ≤ deepBandBudgetR 4 (4 * g) ∧
      ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5 g ≤ deepBandBudgetR 5 (4 * g) := by
  exact ⟨
    deepBandBadCount3_le_deepBandBudgetR g (by omega),
    deepBandBadCount4_le_deepBandBudgetR g (by omega),
    deepBandBadCount5_le_deepBandBudgetR g hg⟩

/-- The stronger half-budget prefix for the r=4 and r=5 closed rungs. -/
theorem closed_prefix_r4_r5_half_deepBandBudgetR (g : ℕ) (hg : 3 ≤ g) :
    2 * ArkLib.ProximityGap.DeepBandR4.deepBandBadCount4 g ≤ deepBandBudgetR 4 (4 * g) ∧
      2 * ArkLib.ProximityGap.DeepBandR5.deepBandBadCount5 g ≤ deepBandBudgetR 5 (4 * g) := by
  exact ⟨
    two_mul_deepBandBadCount4_le_deepBandBudgetR g hg,
    two_mul_deepBandBadCount5_le_deepBandBudgetR g hg⟩

end ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget.closed_prefix_r3_r4_r5_deepBandBudgetR
#print axioms
  ArkLib.ProximityGap.Frontier.R114DemandFloorClosedPrefixGeneralBudget.closed_prefix_r4_r5_half_deepBandBudgetR
