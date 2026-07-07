/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R108QRWeilConcreteClearedScalarSevenPackage

/-!
# LANE B2 (#466 round 109): concrete denominator-cleared scalar QR obstructions

R108 removes the auxiliary `N` from the denominator-cleared QR-Weil scalar target.  This file records
the matching contrapositive: a failed head rung rules out the single concrete inequality

`(|G| + sqrt(q) * A)^2 * #QR ≤ 28 * qrWeilSpectralLowerBudget G`,

and also the fully unfolded version of the QR-Weil lower budget.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A failed head rung rules out the concrete denominator-cleared QR-Weil scalar inequality. -/
theorem not_concrete_cleared_scalar_qrWeil_seven_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) := by
  intro hNum
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.2 r hr)

/-- Same concrete obstruction, with nonnegativity discharged from `A ≥ 0`. -/
theorem not_concrete_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) := by
  intro hNum
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.2 r hr)

/-- A failed head rung rules out the fully unfolded denominator-cleared QR-Weil scalar inequality. -/
theorem not_unfolded_cleared_scalar_qrWeil_seven_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) := by
  intro hNum
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.2 r hr)

/-- Same fully unfolded obstruction, with nonnegativity discharged from `A ≥ 0`. -/
theorem not_unfolded_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) := by
  intro hNum
  exact hfail
    ((awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.2 r hr)

end ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions.not_concrete_cleared_scalar_qrWeil_seven_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions.not_concrete_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions.not_unfolded_cleared_scalar_qrWeil_seven_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R109QRWeilConcreteClearedScalarSevenObstructions.not_unfolded_cleared_scalar_qrWeil_seven_of_A_nonneg_of_headRung_failure
