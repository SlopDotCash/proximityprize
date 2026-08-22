/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R78QRWeilCertificateThresholdAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R78QRWeilNormalizedNumeratorAdapters

/-!
# LANE B2 (#466 round 79): normalized QR Weil certificates with threshold slack

R76 accepts normalized average certificates `S <= N / #QR`; R78 adds certificate monotonicity
in the threshold.  This file packages the common downstream shape:

* certify a stronger normalized threshold `S <= N / #QR`;
* consume a weaker threshold `S' <= S` in the numerator estimate.

This avoids repeating the two-step composition in later finite-prime or analytic certificates.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
open ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters
open ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Normalized QR Weil average data at threshold `S` certify any weaker threshold `S' <= S`. -/
theorem qrWeilAverageCertificate_of_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {G : Finset F} {S S' N : ℝ}
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G) :
    QRWeilAverageCertificate χ G S' N :=
  qrWeilAverageCertificate_mono_threshold
    (F := F) (χ := χ) hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN)

/-- Exact-budget all-rung consumer from normalized data at a stronger threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-final-constant all-rung consumer from normalized data at a stronger threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-numerator all-rung consumer from normalized data at a stronger threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_le_div_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0
    (hS'.trans hS) hN hNum

/-- Larger-numerator and larger-final-constant all-rung consumer from normalized data at a
stronger threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hC'0 hCC
    (hS'.trans hS) hN hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters.qrWeilAverageCertificate_of_le_div_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const

end ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters
