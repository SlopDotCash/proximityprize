/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R100QRWeilSevenPackage
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R79QRWeilNormalizedThresholdAdapters

/-!
# LANE B2 (#466 round 101): normalized constant-seven QR package

R100 exposes the public constant-seven package from a named `QRWeilAverageCertificate`.
R79 builds that certificate from the normalized data usually produced by analytic or finite-prime
work:

`S ≤ N / #QR`, `N ≤ qrWeilSpectralLowerBudget G`, and a weaker downstream threshold `S' ≤ S`.

This file composes those surfaces.  The remaining scalar target is now fully explicit:

* normalized QR supply: `S ≤ N / #QR` and `N ≤ qrWeilSpectralLowerBudget G`,
* numerator payment at the consumed threshold: `B^2 ≤ 7*S'` (or exact-budget variant),
* threshold slack: `S' ≤ S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
open ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters
open ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator constant-seven package from normalized QR data. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Exact-numerator normalized constant-seven package with bridge-budget nonnegativity discharged
from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-numerator constant-seven package from normalized QR data. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-numerator normalized constant-seven package with bridge-budget nonnegativity discharged
from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS'
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

end ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
