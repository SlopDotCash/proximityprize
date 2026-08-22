/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R74QRWeilAverageBudgetBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R74QRNonemptyAverageBridge

/-!
# LANE B2 (#466 round 75): named QR Weil average certificates

R74 turns the R17 QR spectral-weight lower bound into the average-mass socket whenever
`#QR * S <= qrWeilSpectralLowerBudget G`.  Computational and finite-prime certificates often arrive
with an intermediate certified lower number `N`, so this file names the two-step certificate

`#QR * S <= N <= qrWeilSpectralLowerBudget G`

and feeds it through the R73/R74 tower stack, with QR nonemptiness discharged from
`IsRealQuadChar`.

This is certificate plumbing only.  The prize still requires an input strong enough to make the
shifted-Legendre numerator estimate hold at the target scale.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R73QRAveragePointMassBridge
open ArkLib.ProximityGap.Frontier.R74QRNonemptyAverageBridge
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named certificate that an average QR threshold `S` lies below the R17 Weil QR lower bound,
possibly through an intermediate certified lower number `N`. -/
def QRWeilAverageCertificate
    (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1] (G : Finset F) (S N : ℝ) : Prop :=
  ((QRset χ).card : ℝ) * S ≤ N ∧ N ≤ qrWeilSpectralLowerBudget (F := F) G

/-- A named QR Weil average certificate is exactly the budget hypothesis consumed by R74. -/
theorem qrWeilBudget_of_certificate
    [DecidablePred fun b : F => χ b = 1]
    {G : Finset F} {S N : ℝ}
    (hCert : QRWeilAverageCertificate χ G S N) :
    ((QRset χ).card : ℝ) * S ≤ qrWeilSpectralLowerBudget (F := F) G :=
  hCert.1.trans hCert.2

/-- A named certificate feeds the average-mass socket. -/
theorem qrAverageMassLower_of_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S N : ℝ}
    (hCert : QRWeilAverageCertificate χ G S N) :
    QRAverageMassLower χ ψ G S :=
  qrAverageMassLower_of_qrWeilBudget
    (F := F) (χ := χ) hχ hψ (qrWeilBudget_of_certificate hCert)

/-- A named certificate produces a point-mass witness, with QR nonemptiness discharged from
`IsRealQuadChar`. -/
theorem qrPointMassLower_of_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {S N : ℝ}
    (hCert : QRWeilAverageCertificate χ G S N) :
    ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.QRPointMassLower χ ψ G S :=
  qrPointMassLower_of_averageMassLower_quadChar
    (F := F) (χ := χ) hχ (qrAverageMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert)

/-- A named certificate feeds the exact R69 shifted-Legendre tower budget. -/
theorem shiftedLegendreTowerBudget_of_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {A C S N : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_averageMassLower_quadChar
    (F := F) (χ := χ) hχ hB0 hC0
    (qrAverageMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert) hNum

/-- Direct all-rung consumer from a named QR Weil average certificate. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrAverageMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert) hNum

/-- Direct all-rung consumer from a named certificate, with bridge-budget nonnegativity discharged
from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_certificate_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_averageMassLower_quadChar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0
    (qrAverageMassLower_of_certificate (F := F) (χ := χ) hχ hψ hCert) hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.qrWeilBudget_of_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.qrAverageMassLower_of_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.qrPointMassLower_of_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.shiftedLegendreTowerBudget_of_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.tower_qr_of_shiftedLegendreSupBound_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate.tower_qr_of_shiftedLegendreSupBound_certificate_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
