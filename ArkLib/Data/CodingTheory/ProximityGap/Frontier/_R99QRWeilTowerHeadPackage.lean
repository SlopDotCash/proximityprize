/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R85QRWeilAwayTowerNamedThresholdCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R98QRWeilHeadRungWindowConsumers

/-!
# LANE B2 (#466 round 99): QR Weil tower/head package

R85 packages a named QR Weil certificate as `AwaySupBound` plus the whole R19 away tower.
R98 packages the same certificate, when published at `C' ≤ 7`, as every head rung from depth
`3` onward.

This file combines those consequences into one consumer-facing certificate package:

* the fixed-point `AwaySupBound`,
* all later R19 away-tower bounds,
* the head-rung window `∀ r ≥ 3, HeadRungSubWick r`.

The hard input remains unchanged: the shifted-Legendre/Paley certificate proving the QR
`AwaySupBound` at a public constant no larger than `7`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R85QRWeilAwayTowerNamedThresholdCapstone
open ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator named QR Weil certificates at `C' ≤ 7` give the fixed-point sup bound, the
R19 away tower, and every head rung from depth `3` onward. -/
theorem awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) := by
  have hpack :=
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC hS hCert hNum
  have hhead :=
    headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCC hC'7 hS hCert hNum
  exact ⟨hpack.1, hpack.2, hhead⟩

/-- Exact-numerator package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) := by
  have hpack :=
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hC'0 hCC hS hCert hNum
  have hhead :=
    headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hCC hC'7 hS hCert hNum
  exact ⟨hpack.1, hpack.2, hhead⟩

/-- Larger-numerator named QR Weil certificates at `C' ≤ 7` give the fixed-point sup bound, the
R19 away tower, and every head rung from depth `3` onward. -/
theorem awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
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
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) := by
  have hpack :=
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hC'0 hCC hS hCert hNum
  have hhead :=
    headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hC'7 hS hCert hNum
  exact ⟨hpack.1, hpack.2, hhead⟩

/-- Larger-numerator package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
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
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) := by
  have hpack :=
    awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hC'0 hCC hS hCert hNum
  have hhead :=
    headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hCC hC'7 hS hCert hNum
  exact ⟨hpack.1, hpack.2, hhead⟩

end ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage.awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage.awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage.awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage.awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
