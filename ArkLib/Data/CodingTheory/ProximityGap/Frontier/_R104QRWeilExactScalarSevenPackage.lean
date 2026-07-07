/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R103QRWeilScalarSevenPackage

/-!
# LANE B2 (#466 round 104): exact scalar constant-seven QR package

R103 exposes the larger-numerator scalar socket

`B^2 * #QR ≤ 7*N`.

This file records the exact-budget specialization `B = shiftedLegendreIncidenceBudget G A`.
The remaining exact scalar target is:

`shiftedLegendreIncidenceBudget G A ^ 2 * #QR ≤ 7*N`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R103QRWeilScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact scalar constant-seven package: the shifted-Legendre incidence budget itself pays the
cross-multiplied QR numerator inequality. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum :
      shiftedLegendreIncidenceBudget (F := F) G A ^ 2 * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0
    (le_rfl : shiftedLegendreIncidenceBudget (F := F) G A
      ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    hN hNum

/-- Exact scalar constant-seven package with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum :
      shiftedLegendreIncidenceBudget (F := F) G A ^ 2 * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_scalar_le_sq_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0
    (le_rfl : shiftedLegendreIncidenceBudget (F := F) G A
      ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    hN hNum

end ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
