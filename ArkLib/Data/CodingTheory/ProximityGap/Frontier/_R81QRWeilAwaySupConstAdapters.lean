/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R80QRWeilAwaySupBridge

/-!
# LANE B2 (#466 round 81): constant monotonicity for QR Weil `AwaySupBound`

Round 80 exposed the direct QR Weil certificate endpoint as R19's fixed-point proposition
`AwaySupBound`.  This file adds the missing constant-relaxation adapters: a sharp certificate at
constant `C` may be consumed at any larger constant `C'`.

This is useful for downstream prize-facing sockets that keep the analytic/finite certificate sharp
but reserve a more conservative public constant for the wall or tower statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters
open ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters
open ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- `AwaySupBound` is monotone in its constant. -/
theorem awaySupBound_mono_const
    {ψ : AddChar F ℂ} {G H D : Finset F} {C C' : ℝ}
    (hCC : C ≤ C')
    (h : AwaySupBound ψ G H D C) :
    AwaySupBound ψ G H D C' := by
  intro s hs
  have hSig : (0 : ℝ) ≤ ∑ b ∈ H, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _
  exact (h s hs).trans (mul_le_mul_of_nonneg_right hCC hSig)

/-- A named QR Weil certificate can be consumed at any larger `AwaySupBound` constant. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_mono_const (F := F) hCC
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCert hNum)

/-- Larger-numerator QR Weil certificates can be consumed at any larger `AwaySupBound` constant. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_mono_const (F := F) hCC
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCert hNum)

/-- Normalized QR Weil data and a larger numerator can be consumed at any larger constant. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_mono_const (F := F) hCC
    (awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hS hN hNum)

/-- Normalized threshold-slack QR Weil data can be consumed at any larger constant. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_mono_const (F := F) hCC
    (awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hS' hS hN hNum)

/-- Normalized threshold-slack QR Weil data with `A >= 0` can be consumed at any larger constant. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C' :=
  awaySupBound_mono_const (F := F) hCC
    (awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hS' hS hN hNum)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_mono_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R81QRWeilAwaySupConstAdapters
