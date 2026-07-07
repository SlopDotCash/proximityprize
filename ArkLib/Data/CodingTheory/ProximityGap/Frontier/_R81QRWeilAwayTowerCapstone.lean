/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R80QRWeilAwaySupBridge

/-!
# LANE B2 (#466 round 81): QR Weil certificates as fixed-point plus tower certificates

Round 80 landed the direct prize-facing output of the QR Weil certificate language:
`AwaySupBound`.  Round 19 already proves that this fixed-point bound is exactly the input needed
for the whole corrected-B away tower.  This file keeps those two consequences together as a single
certificate consumer, so downstream finite-prime or analytic attempts can target one endpoint and
receive both the fixed-point statement and every rung consequence.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R81QRWeilAwayTowerCapstone

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate plus a shifted-Legendre numerator estimate gives both the
fixed-point `AwaySupBound` and all later R19 away rungs. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C :=
    awaySupBound_qr_of_shiftedLegendreSupBound_certificate
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCert hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC0 hAway⟩

/-- Normalized QR Weil data, threshold slack, and a larger numerator give the fixed-point
`AwaySupBound` plus the whole corrected-B away tower. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C :=
    awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hS' hS hN hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC0 hAway⟩

/-- Same capstone with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C :=
    awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hS' hS hN hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC0 hAway⟩

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwayTowerCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwayTowerCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwayTowerCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R81QRWeilAwayTowerCapstone
