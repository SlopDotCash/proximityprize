/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R87WallGlueBudgetBridge

/-!
# LANE K/I (#466 round 88): optimized natural-budget wall-glue bridge

Round 87 converts the two-sided capstone's natural-budget glue into the wall capstone's normalized
glue.  This file specializes that bridge to the optimized wall-supremum budget
`sqrt(2e * |G| * (log |F| + 1))`, the value supplied by `WallHolds` itself.

The result removes the free `B` parameter from the natural-budget wall capstone: a future
hyperplane-cancellation certificate only has to publish the natural-budget glue at the optimized
wall value.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open scoped NNReal ENNReal
open ProximityGap Code
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.WallCapstone
open ArkLib.ProximityGap.Frontier.TwoSidedCapstone
open ArkLib.ProximityGap.Frontier.R87WallGlueBudgetBridge

namespace ArkLib.ProximityGap.Frontier.R88WallGlueOptimizedBudgetBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The optimized wall capstone consumed from the natural-budget glue used by the two-sided
capstone.  The free char-sum parameter is fixed to the bound supplied by `WallHolds`. -/
theorem wall_capstone_optimized_of_incidenceFromWallGlue_budget
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : Real.exp 1 ≤ (Fintype.card F : ℝ))
    (hwall : WallHolds G)
    (s₀ s₁ : WordStack A (Fin 2) ι → F)
    (hglue : IncidenceFromWallGlue (F := F) (A := A) C δ E G
      (Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (Real.log (Fintype.card F : ℝ) + 1)))
      s₀ s₁)
    (hδ1 : δ ≤ 1) :
    (∀ (r : ℕ) (b : F), b ≠ 0 →
        ‖eta ψ G b‖ ^ (2 * r)
          ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
      ∧ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
          ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  wall_capstone_of_incidenceFromWallGlue_budget C δ E hψ G hwall
    (ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.sqrt_floor_nonneg (F := F) G)
    (ArkLib.ProximityGap.Frontier.MomentOptimizedSupNorm.supNorm_le_of_wallHolds
      (F := F) hψ G hq hwall)
    s₀ s₁ hglue hδ1

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R88WallGlueOptimizedBudgetBridge.wall_capstone_optimized_of_incidenceFromWallGlue_budget

end ArkLib.ProximityGap.Frontier.R88WallGlueOptimizedBudgetBridge
