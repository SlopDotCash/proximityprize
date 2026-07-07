/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R102QRWeilNormalizedSevenNoSlack

/-!
# LANE B2 (#466 round 103): scalar constant-seven QR package

R102 uses the normalized QR threshold `S = N / #QR`.  This file removes `S` from the public
surface.  Since real quadratic characters have a nonempty QR set, the scalar inequality

`B^2 * #QR ≤ 7*N`

implies the no-slack numerator payment

`B^2 ≤ 7 * (N / #QR)`.

The remaining larger-numerator target is now fully cross-multiplied and free of an auxiliary
threshold variable.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R102QRWeilNormalizedSevenNoSlack

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Cross-multiplied scalar numerator payment for the normalized QR threshold `N/#QR`. -/
theorem le_seven_mul_div_card_of_mul_card_le_seven_mul
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {B N : ℝ}
    (hNum : B ^ 2 * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    B ^ 2 ≤ (7 : ℝ) * (N / ((QRset χ).card : ℝ)) := by
  classical
  have hQR : (QRset χ).Nonempty := QRset_nonempty (F := F) (χ := χ) hχ
  have hcard_pos_nat : 0 < (QRset χ).card := Finset.card_pos.mpr hQR
  have hcard_pos : 0 < ((QRset χ).card : ℝ) := by exact_mod_cast hcard_pos_nat
  have hmul :
      B ^ 2 * ((QRset χ).card : ℝ)
        ≤ ((7 : ℝ) * (N / ((QRset χ).card : ℝ))) * ((QRset χ).card : ℝ) := by
    calc
      B ^ 2 * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N := hNum
      _ = ((7 : ℝ) * (N / ((QRset χ).card : ℝ))) * ((QRset χ).card : ℝ) := by
        field_simp [ne_of_gt hcard_pos]
  exact le_of_mul_le_mul_right hmul hcard_pos

/-- Larger-numerator constant-seven package from the scalar QR lower budget, with no auxiliary
threshold `S`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB
    (le_rfl : N / ((QRset χ).card : ℝ) ≤ N / ((QRset χ).card : ℝ))
    hN
    (le_seven_mul_div_card_of_mul_card_le_seven_mul (F := F) (χ := χ) hχ hNum)

/-- Larger-numerator scalar package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB
    (le_rfl : N / ((QRset χ).card : ℝ) ≤ N / ((QRset χ).card : ℝ))
    hN
    (le_seven_mul_div_card_of_mul_card_le_seven_mul (F := F) (χ := χ) hχ hNum)

end ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage.le_seven_mul_div_card_of_mul_card_le_seven_mul
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq
#print axioms
  ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq_of_A_nonneg
