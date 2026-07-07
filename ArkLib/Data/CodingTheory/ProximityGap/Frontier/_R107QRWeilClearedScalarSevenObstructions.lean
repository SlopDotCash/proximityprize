/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R106QRWeilClearedScalarSevenPackage

/-!
# LANE B2 (#466 round 107): denominator-cleared scalar constant-seven QR obstructions

R106 packages the denominator-cleared scalar target

`(|G| + sqrt(q) * A)^2 * #QR ≤ 28*N`

into the public constant-seven away-sup, tower, and head-rung window conclusions.  This file records
the matching contrapositive: a failed head rung rules out the cleared scalar certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R107QRWeilClearedScalarSevenObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R106QRWeilClearedScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A failed head rung rules out the denominator-cleared scalar QR-Weil certificate at constant
`7`. -/
theorem not_cleared_scalar_qrWeil_seven_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (N ≤ qrWeilSpectralLowerBudget (F := F) G ∧
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * N) := by
  rintro ⟨hN, hNum⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_cleared_scalar
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hN hNum).2.2 r hr)

/-- Same denominator-cleared obstruction, with nonnegativity discharged from `A ≥ 0`. -/
theorem not_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (N ≤ qrWeilSpectralLowerBudget (F := F) G ∧
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * N) := by
  rintro ⟨hN, hNum⟩
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_cleared_scalar_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hN hNum).2.2 r hr)

end ArkLib.ProximityGap.Frontier.R107QRWeilClearedScalarSevenObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R107QRWeilClearedScalarSevenObstructions.not_cleared_scalar_qrWeil_seven_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R107QRWeilClearedScalarSevenObstructions.not_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
