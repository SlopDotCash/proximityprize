/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R73QRAveragePointMassBridge

/-!
# LANE B2 (#466 round 74): the R17 QR Weil lower bound feeds the average-mass socket

R17 proves the concrete QR spectral-weight lower bound

`((q * n - n^2 - n^2 * sqrt q) / 2) <= Σ_{b in QR} ‖η_b‖^2`.

R73 introduced the average-mass socket `#QR * S <= Σ_QR`.  This file welds those together: whenever
the desired average threshold `S` is budgeted below the R17 expression, it feeds the point-mass and
tower consumers automatically.

This is still not a prize closure.  The prize-scale obstruction is whether the resulting budget is
large enough simultaneously with the shifted-Legendre sup numerator estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R72QRPointMassBridge
open ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- The concrete R17 QR lower-bound numerator. -/
noncomputable def qrWeilSpectralLowerBudget (G : Finset F) : ℝ :=
  ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
      - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2

/-- If `#QR * S` fits below the R17 QR spectral-weight lower bound, then `S` is an average QR
spectral-mass lower bound. -/
theorem qrAverageMassLower_of_qrWeilBudget
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S : ℝ}
    (hBudget : ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G) :
    QRAverageMassLower χ ψ G S := by
  unfold QRAverageMassLower
  exact hBudget.trans (by
    unfold qrWeilSpectralLowerBudget
    exact qr_weight_lower (F := F) (χ := χ) hχ hψ G)

/-- R17's QR Weil lower bound produces a point-mass witness after the R73 averaging step. -/
theorem qrPointMassLower_of_qrWeilBudget
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S : ℝ}
    (hQR : (QRset χ).Nonempty)
    (hBudget : ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G) :
    QRPointMassLower χ ψ G S :=
  qrPointMassLower_of_averageMassLower
    (F := F) (χ := χ) hQR
    (qrAverageMassLower_of_qrWeilBudget (F := F) (χ := χ) hχ hψ hBudget)

/-- R17's QR Weil lower bound feeds the exact R69 shifted-Legendre tower budget. -/
theorem shiftedLegendreTowerBudget_of_qrWeilBudget
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {A C S : ℝ}
    (hQR : (QRset χ).Nonempty)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hBudget : ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_pointMass
    (F := F) (χ := χ) hB0 hC0
    (qrPointMassLower_of_qrWeilBudget (F := F) (χ := χ) hχ hψ hQR hBudget) hNum

/-- Direct all-rung consumer from the R17 QR Weil lower bound and the shifted-Legendre numerator
estimate. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWeilBudget
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hQR : (QRset χ).Nonempty)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hBudget : ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrPointMassLower_of_qrWeilBudget (F := F) (χ := χ) hχ hψ hQR hBudget) hNum

/-- Direct all-rung consumer from the R17 QR Weil lower bound, with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWeilBudget_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hQR : (QRset χ).Nonempty)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hBudget : ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0
    (qrPointMassLower_of_qrWeilBudget (F := F) (χ := χ) hχ hψ hQR hBudget) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge.qrAverageMassLower_of_qrWeilBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge.qrPointMassLower_of_qrWeilBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge.shiftedLegendreTowerBudget_of_qrWeilBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge.tower_qr_of_shiftedLegendreSupBound_qrWeilBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge.tower_qr_of_shiftedLegendreSupBound_qrWeilBudget_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
