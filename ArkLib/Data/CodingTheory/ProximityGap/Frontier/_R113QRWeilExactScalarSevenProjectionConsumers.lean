/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R104QRWeilExactScalarSevenPackage

/-!
# LANE B2 (#466 round 113): projections for exact-scalar constant-seven QR packages

R104 packages exact-scalar QR data as a triple: `AwaySupBound`, the R19 away tower, and the
head-rung window from depth `3`.  This file exposes the common projections for downstream
consumers that need only one component of that package.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-scalar certificates give the QR `AwaySupBound` projection, with bridge-budget
nonnegativity supplied directly. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hN hNum).1

/-- Exact-scalar certificates give the R19 away-tower projection, with bridge-budget
nonnegativity supplied directly. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hN hNum).2.1

/-- Exact-scalar certificates give the head-rung-window projection, with bridge-budget
nonnegativity supplied directly. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hN hNum).2.2

/-- Exact-scalar certificates give the QR `AwaySupBound` projection, with bridge-budget
nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hN hNum).1

/-- Exact-scalar certificates give the R19 away-tower projection, with bridge-budget
nonnegativity discharged from `A ≥ 0`. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hN hNum).2.1

/-- Exact-scalar certificates give the head-rung-window projection, with bridge-budget
nonnegativity discharged from `A ≥ 0`. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      * ((QRset χ).card : ℝ) ≤ (7 : ℝ) * N) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hN hNum).2.2

end ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_exact_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_exact_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R113QRWeilExactScalarSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
