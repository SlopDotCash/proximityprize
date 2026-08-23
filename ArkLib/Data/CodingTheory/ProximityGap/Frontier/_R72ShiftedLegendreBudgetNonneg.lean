/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R71ShiftedLegendreBudgetMonotonicity

/-!
# LANE B2 (#466 round 72): nonnegativity wrappers for the shifted-Legendre budget

The exact deg-2 bridge budget is

`B(A) = (|G| + sqrt(q) * A) / 2`.

Future Karatsuba-style inputs naturally state `A >= 0`; under that assumption `B(A) >= 0`.
This file packages that arithmetic and removes one nuisance side condition from the R70/R71
mass-lower consumers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge
open ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- The exact shifted-Legendre incidence budget is nonnegative whenever the shifted-Legendre
sup budget `A` is nonnegative. -/
theorem shiftedLegendreIncidenceBudget_nonneg
    (G : Finset F) {A : ℝ} (hA0 : 0 ≤ A) :
    0 ≤ shiftedLegendreIncidenceBudget (F := F) G A := by
  unfold shiftedLegendreIncidenceBudget
  exact div_nonneg
    (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hA0))
    (by norm_num)

/-- R70's mass-lower bridge with the budget nonnegativity discharged from `A >= 0`. -/
theorem shiftedLegendreTowerBudget_of_massLower_of_A_nonneg
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_massLower
    (F := F) (χ := χ) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hMass hNum

/-- Larger-final-constant version of the mass-lower bridge, with budget nonnegativity discharged
from `A >= 0`. -/
theorem shiftedLegendreTowerBudget_of_massLower_le_const_of_A_nonneg
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C C' S : ℝ}
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C' :=
  shiftedLegendreTowerBudget_of_massLower_le_const
    (F := F) (χ := χ) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hCC hMass hNum

/-- Direct all-rung consumer with the budget nonnegativity discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_massLower_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_massLower
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0) hC0 hMass hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg.shiftedLegendreIncidenceBudget_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg.shiftedLegendreTowerBudget_of_massLower_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg.shiftedLegendreTowerBudget_of_massLower_le_const_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg.tower_qr_of_shiftedLegendreSupBound_massLower_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
