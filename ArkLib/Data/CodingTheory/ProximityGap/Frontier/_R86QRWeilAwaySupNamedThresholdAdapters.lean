/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R81QRWeilAwaySupConstAdapters

/-!
# LANE B2 (#466 round 86): named-certificate threshold adapters for `AwaySupBound`

Round 85 packaged named QR Weil threshold slack all the way to `AwaySupBound ∧ tower`.  This file
fills the lower-level fixed-point interface: consumers that only need R19's `AwaySupBound` can use
a named QR Weil average certificate at threshold `S` together with numerator estimates at any
stronger threshold `S' <= S`.

The hard analytic input remains unchanged: a prize-scale shifted-Legendre/Paley-BGK certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters
open ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate at threshold `S` feeds `AwaySupBound` at any larger public
constant when the exact numerator estimate uses any `S' <= S`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- A named QR Weil certificate at threshold `S` and a larger numerator `B` feed `AwaySupBound`
at any larger public constant when the numerator estimate uses any `S' <= S`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Exact-numerator named threshold `AwaySupBound` adapter with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hCC hS hCert hNum

/-- Larger-numerator named threshold `AwaySupBound` adapter with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hB hC0 hCC hS hCert hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters
