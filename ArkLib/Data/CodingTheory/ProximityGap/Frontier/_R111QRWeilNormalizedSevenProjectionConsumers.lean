/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R101QRWeilNormalizedSevenPackage

/-!
# LANE B2 (#466 round 111): projections for normalized constant-seven QR packages

R101 packages normalized QR data as a triple: `AwaySupBound`, the R19 away tower, and the
head-rung window from depth `3`.  This file exposes the common projections so downstream
consumers do not have to destructure the triple manually.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
open ArkLib.ProximityGap.Frontier.R101QRWeilNormalizedSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator normalized data give the QR `AwaySupBound` projection. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS' hS hN hNum).1

/-- Exact-numerator normalized data give the R19 away-tower projection. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS' hS hN hNum).2.1

/-- Exact-numerator normalized data give the head-rung-window projection. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS' hS hN hNum).2.2

/-- Larger-numerator normalized data give the QR `AwaySupBound` projection. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS' hS hN hNum).1

/-- Larger-numerator normalized data give the R19 away-tower projection. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS' hS hN hNum).2.1

/-- Larger-numerator normalized data give the head-rung-window projection. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS' hS hN hNum).2.2

end ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R111QRWeilNormalizedSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
