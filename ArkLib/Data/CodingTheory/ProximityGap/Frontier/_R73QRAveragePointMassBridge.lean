/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R72QRPointMassBridge

/-!
# LANE B2 (#466 round 73): average QR mass produces a point-mass witness

Round 72 lets a single certified QR frequency feed the shifted-Legendre/tower budget.  This file
adds the reverse finite-bookkeeping adapter: a lower bound on the average QR spectral mass produces
such a frequency by the pigeonhole principle.

No cancellation is claimed here.  The open analytic work remains the production of a strong enough
QR mass/average lower bound or shifted-Legendre sup bound; this file only removes the finite maximum
bookkeeping from that future certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R72QRPointMassBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A lower bound for the average QR spectral mass, written without division:
`#QR * S <= Σ_QR ‖η_b‖^2`. -/
def QRAverageMassLower
    (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1]
    (ψ : AddChar F ℂ) (G : Finset F) (S : ℝ) : Prop :=
  ((QRset χ).card : ℝ) * S ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2

/-- A nonempty finite family whose average is at least `S` contains a member at least `S`,
specialized to the QR spectral weights. -/
theorem qrPointMassLower_of_averageMassLower
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {S : ℝ}
    (hQR : (QRset χ).Nonempty)
    (hAvg : QRAverageMassLower χ ψ G S) :
    QRPointMassLower χ ψ G S := by
  classical
  let w : F → ℝ := fun b => ‖eta ψ G b‖ ^ 2
  obtain ⟨b, hb, hmax⟩ := (QRset χ).exists_max_image w hQR
  refine ⟨b, hb, ?_⟩
  have hsum_le : ∑ c ∈ QRset χ, w c ≤ ((QRset χ).card : ℝ) * w b := by
    have hsum := Finset.sum_le_card_nsmul (QRset χ) w (w b) hmax
    simpa [nsmul_eq_mul] using hsum
  have hcard_pos_nat : 0 < (QRset χ).card := Finset.card_pos.mpr hQR
  have hcard_pos : 0 < ((QRset χ).card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hmul : ((QRset χ).card : ℝ) * S ≤ ((QRset χ).card : ℝ) * w b :=
    hAvg.trans hsum_le
  nlinarith

/-- Average QR mass lower bounds are ordinary spectral-mass lower bounds after multiplying by the
cardinality. -/
theorem qrSpectralMassLower_of_averageMassLower
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {S : ℝ}
    (hAvg : QRAverageMassLower χ ψ G S) :
    QRSpectralMassLower χ ψ G (((QRset χ).card : ℝ) * S) :=
  hAvg

/-- Average QR mass lower bounds feed the exact R69 budget through the point-mass adapter. -/
theorem shiftedLegendreTowerBudget_of_averageMassLower
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hQR : (QRset χ).Nonempty)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_pointMass
    (F := F) (χ := χ) hB0 hC0
    (qrPointMassLower_of_averageMassLower (F := F) (χ := χ) hQR hAvg) hNum

/-- Direct all-rung consumer from a shifted-Legendre sup bound and an average QR mass
lower bound. -/
theorem tower_qr_of_shiftedLegendreSupBound_averageMassLower
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hQR : (QRset χ).Nonempty)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrPointMassLower_of_averageMassLower (F := F) (χ := χ) hQR hAvg) hNum

/-- Direct all-rung consumer from an average QR mass lower bound, with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_averageMassLower_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hQR : (QRset χ).Nonempty)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hAvg : QRAverageMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0
    (qrPointMassLower_of_averageMassLower (F := F) (χ := χ) hQR hAvg) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.qrPointMassLower_of_averageMassLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.qrSpectralMassLower_of_averageMassLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.shiftedLegendreTowerBudget_of_averageMassLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.tower_qr_of_shiftedLegendreSupBound_averageMassLower
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.tower_qr_of_shiftedLegendreSupBound_averageMassLower_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge
