/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R73QRAveragePointMassBridge

/-!
# LANE B2 (#466 round 74): QR nonemptiness is automatic for real quadratic characters

Round 73's average-mass bridge needs `(QRset χ).Nonempty` to extract a point mass from an
average lower bound.  For the intended deg-2 socket this is automatic: `1 ∈ QR`, since every
`IsRealQuadChar` has `χ 1 = 1`.

This file removes that finite side condition from the average-mass tower consumers.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- The element `1` belongs to the QR set of any real quadratic character. -/
theorem one_mem_QRset
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1] :
    (1 : F) ∈ QRset χ := by
  simp [QRset, hχ.map_one]

/-- The QR set of a real quadratic character is nonempty. -/
theorem QRset_nonempty
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1] :
    (QRset χ).Nonempty :=
  ⟨1, one_mem_QRset (F := F) (χ := χ) hχ⟩

/-- Average QR mass lower bounds produce point masses without an explicit nonempty side
condition. -/
theorem qrPointMassLower_of_averageMassLower_quadChar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {S : ℝ}
    (hAvg : QRAverageMassLower χ ψ G S) :
    ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.QRPointMassLower χ ψ G S :=
  qrPointMassLower_of_averageMassLower
    (F := F) (χ := χ) (QRset_nonempty (F := F) (χ := χ) hχ) hAvg

/-- Average QR mass lower bounds feed the exact R69 budget for real quadratic characters. -/
theorem shiftedLegendreTowerBudget_of_averageMassLower_quadChar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_averageMassLower
    (F := F) (χ := χ) (QRset_nonempty (F := F) (χ := χ) hχ) hB0 hC0 hAvg hNum

/-- Direct all-rung consumer from a shifted-Legendre sup bound and an average QR mass lower bound,
with QR nonemptiness discharged from `IsRealQuadChar`. -/
theorem tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_averageMassLower
    (F := F) (χ := χ) hχ hψ hW hGD (QRset_nonempty (F := F) (χ := χ) hχ)
    hB0 hC0 hAvg hNum

/-- Direct all-rung consumer from an average QR mass lower bound, with QR nonemptiness and
bridge-budget nonnegativity discharged from `IsRealQuadChar` and `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_averageMassLower_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD (QRset_nonempty (F := F) (χ := χ) hχ)
    hA0 hC0 hAvg hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.one_mem_QRset
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.QRset_nonempty
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.qrPointMassLower_of_averageMassLower_quadChar
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.shiftedLegendreTowerBudget_of_averageMassLower_quadChar
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge.tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge
