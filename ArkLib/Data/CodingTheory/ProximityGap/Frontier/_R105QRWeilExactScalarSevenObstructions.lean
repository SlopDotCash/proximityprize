/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R104QRWeilExactScalarSevenPackage

/-!
# LANE B2 (#466 round 105): exact scalar constant-seven QR obstructions

R104 packages the exact scalar QR-Weil target

`shiftedLegendreIncidenceBudget G A ^ 2 * #QR ≤ 7*N`

into the public constant-seven away-sup, tower, and head-rung window conclusions.  This file records
the corresponding contrapositive: a failed head rung rules out the exact scalar certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R105QRWeilExactScalarSevenObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A failed head rung rules out the exact scalar constant-seven QR budget. -/
theorem not_exact_scalar_qrWeil_seven_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (N ≤ qrWeilSpectralLowerBudget (F := F) G ∧
      shiftedLegendreIncidenceBudget (F := F) G A ^ 2 * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) := by
  rintro ⟨hN, hNum⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hN hNum).2.2 r hr)

/-- Same exact scalar obstruction, with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem not_exact_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (N ≤ qrWeilSpectralLowerBudget (F := F) G ∧
      shiftedLegendreIncidenceBudget (F := F) G A ^ 2 * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) := by
  rintro ⟨hN, hNum⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hN hNum).2.2 r hr)

end ArkLib.ProximityGap.Frontier.R105QRWeilExactScalarSevenObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R105QRWeilExactScalarSevenObstructions.not_exact_scalar_qrWeil_seven_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R105QRWeilExactScalarSevenObstructions.not_exact_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
