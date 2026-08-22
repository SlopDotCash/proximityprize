/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R70ShiftedLegendreMassLowerBridge

/-!
# LANE B2 (#466 round 71): monotonicity for the shifted-Legendre tower budget

R69--R70 expose the deg-2/Karatsuba socket in normalized form.  This file adds the small
monotonicity adapters needed by future estimates:

* a QR spectral-mass lower bound may be weakened;
* a shifted-Legendre tower budget may be consumed at any larger constant;
* the mass-lower bridge may also target any larger final tower constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- QR spectral-mass lower bounds are monotone downward in the claimed lower bound. -/
theorem qrSpectralMassLower_mono
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {S S' : ℝ}
    (hS : S' ≤ S)
    (hMass : QRSpectralMassLower χ ψ G S) :
    QRSpectralMassLower χ ψ G S' :=
  hS.trans hMass

/-- Shifted-Legendre tower budgets are monotone upward in the tower constant. -/
theorem shiftedLegendreTowerBudget_mono_const
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C C' : ℝ}
    (hCC : C ≤ C')
    (hBudget : ShiftedLegendreTowerBudget (χ := χ) ψ G A C) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C' := by
  refine ⟨hBudget.1, ?_⟩
  have hSig : (0 : ℝ) ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  have hmul : C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2
      ≤ C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hCC hSig
  exact hBudget.2.trans hmul

/-- R70's mass-lower bridge may be consumed at any larger tower constant. -/
theorem shiftedLegendreTowerBudget_of_massLower_le_const
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C C' S : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C' :=
  shiftedLegendreTowerBudget_mono_const hCC
    (shiftedLegendreTowerBudget_of_massLower
      (F := F) (χ := χ) hB0 hC0 hMass hNum)

/-- Direct all-rung consumer with a larger final tower constant. -/
theorem tower_qr_of_shiftedLegendreSupBound_massLower_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreTowerBudget
    (F := F) (χ := χ) hχ hψ hW hGD hC'0
    (shiftedLegendreTowerBudget_of_massLower_le_const
      (F := F) (χ := χ) hB0 hC0 hCC hMass hNum)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity.qrSpectralMassLower_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity.shiftedLegendreTowerBudget_mono_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity.shiftedLegendreTowerBudget_of_massLower_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity.tower_qr_of_shiftedLegendreSupBound_massLower_le_const

end ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity
