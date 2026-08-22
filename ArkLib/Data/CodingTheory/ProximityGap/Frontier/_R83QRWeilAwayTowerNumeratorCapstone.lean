/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R82QRWeilAwayTowerConstCapstone

/-!
# LANE B2 (#466 round 83): larger-numerator away-tower capstones

R82 packages the constant-relaxed QR Weil endpoint for the exact and threshold-slack certificate
interfaces.  This file fills the two common middle shapes:

* a named QR Weil certificate with a larger shifted-Legendre numerator `B`;
* normalized QR Weil average data with a larger numerator, without introducing an artificial
  threshold-slack parameter.

Both return the fixed-point `AwaySupBound` and the all-rung tower at the chosen public constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone

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

/-- A named QR Weil certificate with a larger numerator `B` gives both the relaxed fixed-point
`AwaySupBound` and all later R19 away rungs at any larger public constant `C'`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C' :=
    awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hCert hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC'0 hAway⟩

/-- Normalized QR Weil data with a larger numerator gives both the relaxed fixed-point
`AwaySupBound` and all later R19 away rungs at any larger public constant `C'`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 := by
  have hAway :
      AwaySupBound ψ G (QRset χ) D C' :=
    awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hS hN hNum
  exact ⟨hAway, tower_of_awaySupBound ψ G (QRset χ) D hC'0 hAway⟩

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const

end ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone
