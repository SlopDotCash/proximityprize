/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R76QRWeilAverageNormalization
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R77QRWeilCertificateNumeratorAdapters

/-!
# LANE B2 (#466 round 78): normalized QR Weil certificates with numerator slack

R76 accepts normalized average certificates `S <= N / #QR`.  R77 accepts a larger numerator
bound `B` instead of the exact shifted-Legendre incidence budget.  This file combines the two
interfaces, matching the shape of downstream finite-prime and analytic certificates:

* average budget: `S <= N / #QR`, `N <= qrWeilSpectralLowerBudget G`;
* numerator budget: `shiftedLegendreIncidenceBudget G A <= B`, `B ^ 2 <= C * S`.

The output is the same corrected-B all-rung tower consumer.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
open ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Normalized QR Weil average data and a larger numerator `B` feed the exact tower budget. -/
theorem shiftedLegendreTowerBudget_of_le_div_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {A B C S N : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_certificate_le_sq
    (F := F) (χ := χ) hχ hψ hB0 hB hC0
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Direct all-rung consumer from normalized average data and a larger numerator `B`. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-final-constant all-rung consumer from normalized average data and numerator slack. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hC'0 hCC
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Direct all-rung consumer from normalized data and numerator slack, with bridge-budget
nonnegativity discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Larger-final-constant all-rung consumer from normalized data and numerator slack, with
bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hC'0 hCC
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters.shiftedLegendreTowerBudget_of_le_div_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters
