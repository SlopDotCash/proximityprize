/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R76QRWeilCertificateConstAdapters

/-!
# LANE B2 (#466 round 77): larger-numerator consumers for QR Weil certificates

Round 75 names QR Weil average certificates; round 76 lets their tower constants be rounded upward.
This file adds the other standard budget adapter: instead of proving the exact numerator estimate

`shiftedLegendreIncidenceBudget G A ^ 2 <= C * S`,

it is enough to provide a larger explicit numerator bound `B` with

`shiftedLegendreIncidenceBudget G A <= B` and `B ^ 2 <= C * S`.

This matches the existing R70 mass-lower pattern and keeps future finite/numeric certificates from
having to normalize directly against the exact square.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilCertificateConstAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Convert a larger numerator bound `B` into the exact square needed by R75. -/
theorem shiftedLegendreIncidenceBudget_sq_le_of_le_sq
    {G : Finset F} {A B R : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hNum : B ^ 2 ≤ R) :
    shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ R := by
  exact (pow_le_pow_left₀ hB0 hB 2).trans hNum

/-- A QR Weil certificate feeds the exact R69 budget from a larger explicit numerator `B`. -/
theorem shiftedLegendreTowerBudget_of_certificate_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {A B C S N : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_certificate
    (F := F) (χ := χ) hχ hψ hB0 hC0 hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq (F := F) hB0 hB hNum)

/-- Direct all-rung consumer from a QR Weil certificate and a larger explicit numerator `B`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq (F := F) hB0 hB hNum)

/-- Larger-final-constant tower consumer from a QR Weil certificate and a larger numerator `B`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq (F := F) hB0 hB hNum)

/-- Direct all-rung consumer from a larger numerator `B`, with nonnegativity discharged from
`A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq
      (F := F) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0) hB hNum)

/-- Larger-final-constant tower consumer from a larger numerator `B`, with nonnegativity discharged
from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_certificate_le_const_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hC'0 hCC hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq
      (F := F) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0) hB hNum)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.shiftedLegendreIncidenceBudget_sq_le_of_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.shiftedLegendreTowerBudget_of_certificate_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters.tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters
