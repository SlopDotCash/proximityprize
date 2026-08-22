/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R77QRWeilCertificateNumeratorAdapters

/-!
# LANE B2 (#466 round 78): threshold monotonicity for QR Weil certificates

The R75 certificate records that an average QR threshold `S` fits below a certified lower number:

`#QR * S <= N <= qrWeilSpectralLowerBudget G`.

This file adds the monotonicity adapters in the threshold `S`: a certificate for a stronger
threshold `S` also certifies any weaker threshold `S' <= S`.  This lets downstream consumers choose
more conservative normalized thresholds without redoing the finite QR bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters
open ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- QR Weil average certificates are monotone in the threshold: a certificate for `S` also
certifies every `S' <= S`. -/
theorem qrWeilAverageCertificate_mono_threshold
    [DecidablePred fun b : F => χ b = 1]
    {G : Finset F} {S S' N : ℝ}
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N) :
    QRWeilAverageCertificate χ G S' N := by
  refine ⟨?_, hCert.2⟩
  exact (mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)).trans hCert.1

/-- Exact-budget tower consumer using a stronger certificate threshold than the downstream
numerator threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-final-constant tower consumer using a stronger certificate threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-numerator tower consumer using a stronger certificate threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

/-- Larger-numerator and larger-final-constant tower consumer using a stronger certificate
threshold. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
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
  tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hC'0 hCC
    (qrWeilAverageCertificate_mono_threshold (F := F) (χ := χ) hS hCert) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters.qrWeilAverageCertificate_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const

end ArkLib.ProximityGap.Frontier.R78QRWeilCertificateThresholdAdapters
