/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R69ShiftedLegendreTowerBudget

/-!
# LANE B2 (#466 round 70): split the shifted-Legendre tower budget by spectral mass

Round 69 names the exact tower budget

`B(A)^2 <= C * Σ_QR`, where `B(A) = (|G| + sqrt(q) * A) / 2`.

This file separates the remaining analytic work into two independently reusable pieces:

* a lower bound `S <= Σ_QR` for the QR spectral mass;
* a numerator estimate `B(A)^2 <= C * S`.

Together they produce the R69 `ShiftedLegendreTowerBudget`, and therefore all later QR away
rungs.  This is still conditional on the real analytic estimate, but the normalization target is
now completely explicit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A reusable lower bound for the QR spectral mass `Σ_QR`. -/
def QRSpectralMassLower
    (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1]
    (ψ : AddChar F ℂ) (G : Finset F) (S : ℝ) : Prop :=
  S ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2

/-- A spectral-mass lower bound converts a numerator estimate against `S` into the exact R69
shifted-Legendre tower budget. -/
theorem shiftedLegendreTowerBudget_of_massLower
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  ⟨hB0, hNum.trans (mul_le_mul_of_nonneg_left hMass hC0)⟩

/-- Version with a larger explicit numerator budget `B`. -/
theorem shiftedLegendreTowerBudget_of_le_sq_massLower
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A B C S : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : B ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C := by
  refine shiftedLegendreTowerBudget_of_massLower
    (F := F) (χ := χ) hB0 hC0 hMass ?_
  have hsq : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hB0 hB 2
  exact hsq.trans hNum

/-- A shifted-Legendre sup bound, a QR spectral-mass lower bound, and the corresponding numerator
estimate feed every later deg-2 QR away rung. -/
theorem tower_qr_of_shiftedLegendreSupBound_massLower
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hMass : QRSpectralMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreTowerBudget
    (F := F) (χ := χ) hχ hψ hW hGD hC0
    (shiftedLegendreTowerBudget_of_massLower
      (F := F) (χ := χ) hB0 hC0 hMass hNum)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge.shiftedLegendreTowerBudget_of_massLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge.shiftedLegendreTowerBudget_of_le_sq_massLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge.tower_qr_of_shiftedLegendreSupBound_massLower

end ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge
