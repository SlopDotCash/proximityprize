/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R81QRWeilAwaySupConstAdapters

/-!
# LANE B2 (#466 round 82): constant-relaxed QR Weil away-tower capstones

R80 exposes QR Weil certificates as the fixed-point `AwaySupBound`.  R81 makes that fixed-point
monotone in the public constant.  This file packages the downstream consequence: a sharp
certificate at `C` and a relaxation `C <= C'` produce both `AwaySupBound C'` and the all-rung tower
with the same relaxed constant `C'`.

The hard input remains the prize-scale Paley/BGK cancellation certificate; this file only removes
API friction around how that certificate is consumed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate gives both the relaxed fixed-point `AwaySupBound` and all later
R19 away rungs at any larger constant `C'`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C' :=
    awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCC hCert hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC'0 hAway⟩

/-- Normalized QR Weil data, threshold slack, and a larger numerator give the relaxed fixed-point
plus the whole corrected-B away tower at any larger constant `C'`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
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
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C' :=
    awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hS' hS hN hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC'0 hAway⟩

set_option linter.style.longLine false in
/-- Same relaxed capstone with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C' :=
    awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hCC hS' hS hN hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC'0 hAway⟩

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone
