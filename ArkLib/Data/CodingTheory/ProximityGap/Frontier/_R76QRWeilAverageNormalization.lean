/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R75QRWeilBudgetCertificate

/-!
# LANE B2 (#466 round 76): normalized QR Weil average certificates

R75 names the certificate

`#QR * S <= N <= qrWeilSpectralLowerBudget G`.

This file adds the normalized entry point that finite-prime and analytic certificates usually
produce: a per-frequency average threshold `S <= N / #QR`.  For real quadratic characters the QR
set is nonempty, so the division is harmless and feeds the R75 tower consumers directly.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A normalized per-QR average threshold yields the R75 certificate. -/
theorem qrWeilAverageCertificate_of_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {G : Finset F} {S N : ℝ}
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G) :
    QRWeilAverageCertificate χ G S N := by
  classical
  have hQR : (QRset χ).Nonempty := QRset_nonempty (F := F) (χ := χ) hχ
  have hcard_pos_nat : 0 < (QRset χ).card := Finset.card_pos.mpr hQR
  have hcard_pos : 0 < ((QRset χ).card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hmul :
      ((QRset χ).card : ℝ) * S ≤
        ((QRset χ).card : ℝ) * (N / ((QRset χ).card : ℝ)) :=
    mul_le_mul_of_nonneg_left hS hcard_pos.le
  have hcancel :
      ((QRset χ).card : ℝ) * (N / ((QRset χ).card : ℝ)) = N := by
    field_simp [ne_of_gt hcard_pos]
  exact ⟨hmul.trans_eq hcancel, hN⟩

/-- The normalized certificate feeds the average-mass socket. -/
theorem qrAverageMassLower_of_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S N : ℝ}
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G) :
    ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge.QRAverageMassLower χ ψ G S :=
  qrAverageMassLower_of_certificate
    (F := F) (χ := χ) hχ hψ (qrWeilAverageCertificate_of_le_div hχ hS hN)

/-- The normalized certificate produces a QR point-mass witness. -/
theorem qrPointMassLower_of_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S N : ℝ}
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G) :
    ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.QRPointMassLower χ ψ G S :=
  qrPointMassLower_of_certificate
    (F := F) (χ := χ) hχ hψ (qrWeilAverageCertificate_of_le_div hχ hS hN)

/-- The normalized certificate feeds the exact shifted-Legendre tower budget. -/
theorem shiftedLegendreTowerBudget_of_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {A C S N : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_certificate
    (F := F) (χ := χ) hχ hψ hB0 hC0
    (qrWeilAverageCertificate_of_le_div hχ hS hN) hNum

/-- Direct all-rung consumer from the normalized QR Weil average certificate. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrWeilAverageCertificate_of_le_div hχ hS hN) hNum

/-- Direct all-rung consumer from the normalized certificate, with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0
    (qrWeilAverageCertificate_of_le_div hχ hS hN) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.qrWeilAverageCertificate_of_le_div
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.qrAverageMassLower_of_le_div
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.qrPointMassLower_of_le_div
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.shiftedLegendreTowerBudget_of_le_div
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.tower_qr_of_shiftedLegendreSupBound_le_div
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization.tower_qr_of_shiftedLegendreSupBound_le_div_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
