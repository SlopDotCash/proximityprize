/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._MomentWallWiringCheck
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R88WallGlueOptimizedBudgetBridge

/-!
# LANE M/K/I (#466 round 89): moment-wall wiring with natural-budget glue

`_MomentWallWiringCheck` is the historical R13 wrapper showing that `WallHolds` supplies the
optimized sup-norm parameter consumed by the wall capstone.  R88 exposes the same optimized
capstone through the two-sided capstone's natural-budget glue.

This file gives that R13-facing theorem directly: `WallHolds` plus a natural-budget
`IncidenceFromWallGlue` certificate at the optimized wall value pins the same capstone conclusion
at public error `E / q`.
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
open ArkLib.ProximityGap.Frontier.R88WallGlueOptimizedBudgetBridge

namespace ArkLib.ProximityGap.Frontier.R89MomentWallNaturalBudgetBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- R13 moment-wall wiring, but with the R14/R88 natural-budget glue interface. -/
theorem wall_capstone_moment_closed_of_incidenceFromWallGlue_budget
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
  wall_capstone_optimized_of_incidenceFromWallGlue_budget
    (F := F) (A := A) C δ E hψ G hq hwall s₀ s₁ hglue hδ1

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R89MomentWallNaturalBudgetBridge.wall_capstone_moment_closed_of_incidenceFromWallGlue_budget

end ArkLib.ProximityGap.Frontier.R89MomentWallNaturalBudgetBridge
