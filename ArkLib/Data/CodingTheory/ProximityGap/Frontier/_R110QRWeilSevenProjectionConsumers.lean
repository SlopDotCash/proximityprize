/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R100QRWeilSevenPackage

/-!
# LANE B2 (#466 round 110): projection consumers for the constant-seven QR package

R100 packages the constant-seven QR/shifted-Legendre certificate as a triple:

* `AwaySupBound`,
* the R19 away tower,
* every head rung from depth `3` onward.

This file exposes the common projections for the `A ≥ 0` exact-numerator and larger-numerator
forms, so downstream consumers can ask for the exact consequence they need without destructuring
the package by hand.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R100QRWeilSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator constant-seven certificates give the QR `AwaySupBound` projection, with
bridge-budget nonnegativity supplied directly. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS hCert hNum).1

/-- Exact-numerator constant-seven certificates give the R19 away-tower projection, with
bridge-budget nonnegativity supplied directly. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS hCert hNum).2.1

/-- Exact-numerator constant-seven certificates give the head-rung-window projection, with
bridge-budget nonnegativity supplied directly. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hS hCert hNum).2.2

/-- Exact-numerator constant-seven certificates give the QR `AwaySupBound` projection. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hS hCert hNum).1

/-- Exact-numerator constant-seven certificates give the R19 away-tower projection. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hS hCert hNum).2.1

/-- Exact-numerator constant-seven certificates give the head-rung-window projection. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hS hCert hNum).2.2

/-- Larger-numerator constant-seven certificates give the QR `AwaySupBound` projection, with
bridge-budget nonnegativity supplied directly. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS hCert hNum).1

/-- Larger-numerator constant-seven certificates give the R19 away-tower projection, with
bridge-budget nonnegativity supplied directly. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS hCert hNum).2.1

/-- Larger-numerator constant-seven certificates give the head-rung-window projection, with
bridge-budget nonnegativity supplied directly. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hS hCert hNum).2.2

/-- Larger-numerator constant-seven certificates give the QR `AwaySupBound` projection. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS hCert hNum).1

/-- Larger-numerator constant-seven certificates give the R19 away-tower projection. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS hCert hNum).2.1

/-- Larger-numerator constant-seven certificates give the head-rung-window projection. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ (7 : ℝ) * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hS hCert hNum).2.2

end ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R110QRWeilSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_of_A_nonneg
