/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R78QRWeilCertificateThresholdAdapters

/-!
# LANE B2 (#466 round 79): `A >= 0` threshold-monotone certificate consumers

Round 78 added threshold monotonicity for QR Weil average certificates.  This file adds the
corresponding wrappers where the nonnegativity of the exact shifted-Legendre bridge budget is
discharged from the simpler hypothesis `A >= 0`.

These are still certificate adapters only: the hard input remains the prize-scale shifted-Legendre /
Paley-BGK cancellation estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters
open ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters
open ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-budget threshold-monotone tower consumer with bridge-budget nonnegativity discharged from
`A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-final-constant threshold-monotone tower consumer with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-numerator threshold-monotone tower consumer with bridge-budget nonnegativity discharged
from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-numerator and larger-final-constant threshold-monotone tower consumer with
bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R79QRWeilThresholdANonnegAdapters
