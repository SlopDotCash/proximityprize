/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R101QRWeilNormalizedSevenPackage

/-!
# LANE B2 (#466 round 102): no-slack normalized constant-seven QR package

R101 accepts normalized QR supply at a threshold `S` and consumes any weaker threshold `S' ≤ S`.
This file records the common no-slack specialization `S' = S`.

The remaining certificate now has only one QR threshold:

* `S ≤ N / #QR`,
* `N ≤ qrWeilSpectralLowerBudget G`,
* `shiftedLegendreIncidenceBudget G A ^ 2 ≤ 7*S`
  (or the larger-numerator variant `B^2 ≤ 7*S`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator constant-seven package from normalized QR data, with no threshold slack. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 (le_rfl : S ≤ S) hS hN hNum

/-- Exact-numerator no-slack package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 (le_rfl : S ≤ S) hS hN hNum

/-- Larger-numerator constant-seven package from normalized QR data, with no threshold slack. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB (le_rfl : S ≤ S) hS hN hNum

/-- Larger-numerator no-slack package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB (le_rfl : S ≤ S) hS hN hNum

end ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
