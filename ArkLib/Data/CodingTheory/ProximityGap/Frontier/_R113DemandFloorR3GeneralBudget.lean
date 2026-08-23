/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR3Bound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R109DemandFloorGeneralBudgetBridge

/-!
# Closed r=3 count in the general workbench budget

The workbench identifies the r=3 deep-band theorem as the proven base instance of the proposed
general-r census domination statement.  This file exposes that base theorem using the same
`deepBandBudgetR r n = 2^r * C(n/2,r)` interface as the later r=4/r=5 adapters.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R113DemandFloorR3GeneralBudget

open ArkLib.ProximityGap.Frontier.R109DemandFloorGeneralBudgetBridge

/-- The general workbench budget at `r = 3`, `n = 4g`, is the named r=3 budget. -/
theorem deepBandBudgetR_three_eq_deepBandBudget (g : ℕ) :
    deepBandBudgetR 3 (4 * g) = ArkLib.ProximityGap.DeepBandR3.deepBandBudget g := by
  rw [deepBandBudgetR_four_mul]
  rfl

/-- The closed r=3 count satisfies the general workbench budget at `n = 4g`. -/
theorem deepBandBadCount3_le_deepBandBudgetR (g : ℕ) (hg : 2 ≤ g) :
    ArkLib.ProximityGap.DeepBandR3.deepBandBadCount g ≤ deepBandBudgetR 3 (4 * g) := by
  rw [deepBandBudgetR_three_eq_deepBandBudget]
  exact ArkLib.ProximityGap.DeepBandR3.deepBandBadCount_le_budget g hg

end ArkLib.ProximityGap.Frontier.R113DemandFloorR3GeneralBudget

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R113DemandFloorR3GeneralBudget.deepBandBudgetR_three_eq_deepBandBudget
#print axioms
  ArkLib.ProximityGap.Frontier.R113DemandFloorR3GeneralBudget.deepBandBadCount3_le_deepBandBudgetR
