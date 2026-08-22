/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R75QRWeilBudgetCertificate

/-!
# LANE B2 (#466 round 76): larger-constant consumers for QR Weil certificates

Round 75 packages QR Weil average certificates in the form

`#QR * S <= N <= qrWeilSpectralLowerBudget G`.

This file adds the standard larger-final-constant adapters: a certificate and numerator estimate
proved with constant `C` can feed a tower stated with any `C' >= C`.  This matches downstream
normalization practice, where constants are often rounded upward after local estimates are composed.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72QRPointMassBridge
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A QR Weil certificate feeds the all-rung tower with any larger final constant. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC
    (qrPointMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert) hNum

/-- Larger-final-constant QR Weil certificate consumer with bridge-budget nonnegativity discharged
from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hC'0 hCC
    (qrPointMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters
