/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R99QRWeilTowerHeadPackage

/-!
# LANE B2 (#466 round 100): the public constant-seven QR package

R99 packages the QR/shifted-Legendre route at any public constant `C' ≤ 7`.  This file exposes the
literal prize-facing socket with `C = C' = 7`, discharging the routine constant side conditions.

Thus the remaining analytic certificate has the clean form:

* a shifted-Legendre sup bound,
* a named QR Weil average certificate at threshold `S`,
* a numerator inequality at the stronger threshold `S' ≤ S`,

`shiftedLegendreIncidenceBudget G A ^ 2 ≤ 7 * S'`

(or the corresponding larger-numerator variant).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R99QRWeilTowerHeadPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator named QR Weil certificates at the public constant `7` give the fixed-point
sup bound, the R19 away tower, and every head rung from depth `3` onward. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0
    (by norm_num : (0 : ℝ) ≤ 7)
    (by norm_num : (0 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    hS hCert hNum

/-- Exact-numerator constant-seven package with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0
    (by norm_num : (0 : ℝ) ≤ 7)
    (by norm_num : (0 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    hS hCert hNum

/-- Larger-numerator named QR Weil certificates at public constant `7` give the fixed-point sup
bound, the R19 away tower, and every head rung from depth `3` onward. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB
    (by norm_num : (0 : ℝ) ≤ 7)
    (by norm_num : (0 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    hS hCert hNum

/-- Larger-numerator constant-seven package with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB
    (by norm_num : (0 : ℝ) ≤ 7)
    (by norm_num : (0 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    (le_rfl : (7 : ℝ) ≤ 7)
    hS hCert hNum

end ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
