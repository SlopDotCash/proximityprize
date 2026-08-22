/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R106QRWeilClearedScalarSevenPackage

/-!
# LANE B2 (#466 round 108): concrete denominator-cleared scalar QR package

R106 leaves the QR spectral lower budget as a named auxiliary `N`.
This file specializes `N` to the concrete R17 QR-Weil lower-budget expression:

`((q * |G| - |G|^2 - |G|^2 * sqrt(q)) / 2)`.

The remaining arithmetic target is now the single denominator-cleared inequality

`(|G| + sqrt(q) * A)^2 * #QR ≤ 28 * qrWeilSpectralLowerBudget G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R106QRWeilClearedScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Concrete denominator-cleared scalar constant-seven package, with the QR-Weil spectral lower
budget used directly. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0
    (le_rfl : qrWeilSpectralLowerBudget (F := F) G
      ≤ qrWeilSpectralLowerBudget (F := F) G)
    hNum

/-- Concrete denominator-cleared scalar package with nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0
    (le_rfl : qrWeilSpectralLowerBudget (F := F) G
      ≤ qrWeilSpectralLowerBudget (F := F) G)
    hNum

/-- Fully unfolded denominator-cleared scalar package. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0
    (by simpa [qrWeilSpectralLowerBudget] using hNum)

/-- Fully unfolded denominator-cleared scalar package, with nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0
    (by simpa [qrWeilSpectralLowerBudget] using hNum)

end ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
