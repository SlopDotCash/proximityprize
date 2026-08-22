/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WallCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._TwoSidedCapstone

/-!
# LANE K/I (#466 round 87): natural-budget wall-glue bridge

The wall capstone packages its residual incidence glue as an ENNReal-normalized budget
`(charSumIncidenceBudget G B) / q <= epsilon*`.  The two-sided capstone's named glue uses the more
certificate-facing natural budget `charSumIncidenceBudget G B <= E`.

This file records the one-way adapter from the natural-budget glue to the normalized wall glue, and
then feeds it into the existing wall capstone.  It adds no analytic content; the hyperplane
cancellation remains the named open input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

open scoped NNReal ENNReal
open ProximityGap Code
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.CharSumDeltaStarBridge
open ArkLib.ProximityGap.Frontier.WallCapstone
open ArkLib.ProximityGap.Frontier.TwoSidedCapstone

namespace ArkLib.ProximityGap.Frontier.R87WallGlueBudgetBridge

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The two-sided capstone's natural-budget glue feeds the wall capstone's normalized-budget glue
at public error `E / q`. -/
theorem realizedIncidenceBudget_of_incidenceFromWallGlue_budget
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ) (G : Finset F) (B : ℝ)
    (s₀ s₁ : WordStack A (Fin 2) ι → F)
    (hglue : IncidenceFromWallGlue (F := F) (A := A) C δ E G B s₀ s₁) :
    RealizedIncidenceBudget C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ G B s₀ s₁ := by
  refine ⟨hglue.1, ?_⟩
  gcongr
  exact_mod_cast hglue.2

/-- Wall capstone consumed from the natural-budget glue used by the two-sided capstone. -/
theorem wall_capstone_of_incidenceFromWallGlue_budget
    (C : Set (ι → A)) (δ : ℝ≥0) (E : ℕ)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hwall : WallHolds G)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ B)
    (s₀ s₁ : WordStack A (Fin 2) ι → F)
    (hglue : IncidenceFromWallGlue (F := F) (A := A) C δ E G B s₀ s₁)
    (hδ1 : δ ≤ 1) :
    (∀ (r : ℕ) (b : F), b ≠ 0 →
        ‖eta ψ G b‖ ^ (2 * r)
          ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r))
      ∧ δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := A) C
          ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) :=
  wall_capstone C ((E : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)) δ hψ G hwall
    hB0 hB s₀ s₁
    (realizedIncidenceBudget_of_incidenceFromWallGlue_budget C δ E G B s₀ s₁ hglue)
    hδ1

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R87WallGlueBudgetBridge.realizedIncidenceBudget_of_incidenceFromWallGlue_budget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R87WallGlueBudgetBridge.wall_capstone_of_incidenceFromWallGlue_budget

end ArkLib.ProximityGap.Frontier.R87WallGlueBudgetBridge
