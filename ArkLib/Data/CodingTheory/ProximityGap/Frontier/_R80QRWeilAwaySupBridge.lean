/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R67Deg2SupToAwayTower
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R72ShiftedLegendreBudgetNonneg
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R79QRWeilNormalizedThresholdAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R79QRWeilThresholdANonnegAdapters

/-!
# LANE B2 (#466 round 80): QR Weil certificates feed `AwaySupBound` directly

Rounds 75--79 package QR Weil average certificates into all-rung tower consumers.  R67 is the
earlier, more primitive prize-facing socket: a shifted-Legendre sup bound plus a normalized
square budget yields `AwaySupBound` itself, before applying the R19 tower recursion.

This file exposes that direct endpoint for the normalized QR Weil certificate language.  It is still
certificate plumbing, but the output is the wall's fixed-point statement rather than only the
derived rung inequalities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R76QRWeilAverageNormalization
open ArkLib.ProximityGap.Frontier.R77QRWeilCertificateNumeratorAdapters
open ArkLib.ProximityGap.Frontier.R78QRWeilNormalizedNumeratorAdapters
open ArkLib.ProximityGap.Frontier.R79QRWeilNormalizedThresholdAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate plus a shifted-Legendre numerator estimate feeds
`AwaySupBound` directly. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C := by
  have hBudget :
      ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
    shiftedLegendreTowerBudget_of_certificate
      (F := F) (χ := χ) hχ hψ hB0 hC0 hCert hNum
  have hBridge :
      (G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2
        ≤ shiftedLegendreIncidenceBudget (F := F) G A := by
    refine le_of_eq ?_
    unfold shiftedLegendreIncidenceBudget
    ring
  exact awaySupBound_qr_of_shiftedLegendreSupBound
    (F := F) (χ := χ) hχ hψ (G := G) (D := D) (A := A)
    (B := shiftedLegendreIncidenceBudget (F := F) G A) (C := C)
    hW hGD hBridge hBudget.1 hBudget.2

/-- A named QR Weil certificate plus a larger numerator `B` feeds `AwaySupBound` directly. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCert
    (shiftedLegendreIncidenceBudget_sq_le_of_le_sq (F := F) hB0 hB hNum)

/-- Normalized QR Weil data and a larger numerator `B` feed `AwaySupBound` directly. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq
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
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0
    (qrWeilAverageCertificate_of_le_div (F := F) (χ := χ) hχ hS hN) hNum

/-- Normalized QR Weil data at a stronger threshold `S` feed `AwaySupBound` at any weaker
threshold `S' <= S`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0
    (qrWeilAverageCertificate_of_le_div_mono_threshold
      (F := F) (χ := χ) hχ hS' hS hN) hNum

/-- Normalized QR Weil data at a stronger threshold feed `AwaySupBound`, with bridge-budget
nonnegativity discharged from `A >= 0`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hS' : S' ≤ S)
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S') :
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hB hC0 hS' hS hN hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge.awaySupBound_qr_of_shiftedLegendreSupBound_certificate
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge.awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge.awaySupBound_qr_of_shiftedLegendreSupBound_le_div_le_sq_mono_threshold_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R80QRWeilAwaySupBridge
