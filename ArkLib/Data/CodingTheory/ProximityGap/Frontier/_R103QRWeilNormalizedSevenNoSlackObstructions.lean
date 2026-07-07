/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R102QRWeilNormalizedSevenNoSlack

/-!
# LANE B2 (#466 round 103): no-slack normalized constant-seven obstructions

R102 exposes the normalized constant-seven package in the single-threshold form `S' = S`.
This file records the matching contrapositive: a failed head rung rules out the no-slack
normalized scalar certificate at that threshold.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A failed head rung rules out exact-numerator no-slack normalized QR data at constant `7`. -/
theorem not_noSlack_normalized_qrWeil_seven_exact_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hS hN hNum).2.2 r hr)

/-- Same no-slack exact-numerator obstruction, with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem not_noSlack_normalized_qrWeil_seven_exact_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hS hN hNum).2.2 r hr)

/-- A failed head rung rules out larger-numerator no-slack normalized QR data at constant `7`. -/
theorem not_noSlack_normalized_qrWeil_seven_le_sq_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS hN hNum).2.2 r hr)

/-- Same no-slack larger-numerator obstruction, with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem not_noSlack_normalized_qrWeil_seven_le_sq_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS hN hNum).2.2 r hr)

end ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions.not_noSlack_normalized_qrWeil_seven_exact_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions.not_noSlack_normalized_qrWeil_seven_exact_of_A_nonneg_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions.not_noSlack_normalized_qrWeil_seven_le_sq_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilNormalizedSevenNoSlackObstructions.not_noSlack_normalized_qrWeil_seven_le_sq_of_A_nonneg_of_headRung_failure
