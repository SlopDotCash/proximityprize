/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R82QRWeilAwayTowerConstCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R83QRWeilAwayTowerNumeratorCapstone

/-!
# LANE B2 (#466 round 85): named-certificate threshold away-tower capstones

The normalized threshold-slack interface already reached the combined endpoint
`AwaySupBound ∧ tower` in R82.  This file fills the same socket for named QR Weil average
certificates: a certificate at threshold `S` can be consumed by numerator estimates at any
stronger threshold `S' <= S`.

This remains API plumbing around the Paley/BGK wall; the hard input is still the shifted-Legendre
sup bound plus the QR Weil average certificate at prize scale.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters
open ArkLib.ProximityGap.Frontier.R82QRWeilAwayTowerConstCapstone
open ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate at threshold `S` gives the relaxed fixed-point `AwaySupBound`
and all later R19 away rungs when the exact numerator estimate uses any `S' <= S`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-numerator named QR Weil certificates at threshold `S` give the relaxed fixed-point
`AwaySupBound` and all later R19 away rungs when the numerator estimate uses `S' <= S`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
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
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

set_option linter.style.longLine false in
/-- Exact-numerator threshold capstone with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hC'0 hCC hS hCert hNum

set_option linter.style.longLine false in
/-- Larger-numerator threshold capstone with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
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
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hB hC0 hC'0 hCC hS hCert hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone
