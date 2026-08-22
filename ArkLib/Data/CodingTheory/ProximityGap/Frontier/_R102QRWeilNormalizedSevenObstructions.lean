/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R101QRWeilNormalizedSevenPackage

/-!
# LANE B2 (#466 round 102): normalized constant-seven obstructions

R101 turns normalized QR data into the public constant-seven package.  This file records the
contrapositive at the normalized-data level: if a head rung from depth `3` onward fails, then the
normalized scalar supply `S ≤ N / #QR` together with `N ≤ qrWeilSpectralLowerBudget G` cannot
coexist with the same numerator payment.

This is the audit-facing form for finite-prime and analytic certificates, where the QR certificate
is usually produced through normalized lower-budget data rather than as a named proposition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A failed head rung rules out exact-numerator normalized QR data at constant `7`. -/
theorem not_normalized_qrWeil_seven_exact_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS' : S' ≤ S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hS' hS hN hNum).2.2 r hr)

/-- Same exact-numerator obstruction, with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem not_normalized_qrWeil_seven_exact_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS' : S' ≤ S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hS' hS hN hNum).2.2 r hr)

/-- A failed head rung rules out larger-numerator normalized QR data at constant `7`. -/
theorem not_normalized_qrWeil_seven_le_sq_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS' hS hN hNum).2.2 r hr)

/-- Same larger-numerator obstruction, with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem not_normalized_qrWeil_seven_le_sq_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (S ≤ N / ((QRset χ).card : ℝ) ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G) := by
  rintro ⟨hS, hN⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS' hS hN hNum).2.2 r hr)

end ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions.not_normalized_qrWeil_seven_exact_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions.not_normalized_qrWeil_seven_exact_of_A_nonneg_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions.not_normalized_qrWeil_seven_le_sq_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenObstructions.not_normalized_qrWeil_seven_le_sq_of_A_nonneg_of_headRung_failure
