/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R86QRWeilAwaySupNamedThresholdAdapters
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R97HeadRungWindowConsumers

/-!
# LANE B2 (#466 round 98): QR Weil certificates feed head-rung windows

R97 records the bypass around the bare successor-recursion obstruction: once an `AwaySupBound C`
has `C ≤ 7`, every head rung from depth `3` onward is automatic.  R86 is the named QR
Weil/shifted-Legendre interface producing `AwaySupBound`.

This file composes the two surfaces.  A future shifted-Legendre/Paley certificate that proves the
QR `AwaySupBound` at public constant `≤ 7` now lands directly as the whole head-rung window
`∀ r ≥ 3, HeadRungSubWick r`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R86QRWeilAwaySupNamedThresholdAdapters
open ArkLib.ProximityGap.Frontier.R97HeadRungWindowConsumers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Exact-numerator QR Weil certificates at public constant `C ≤ 7` supply every head rung from
depth `3` onward. -/
theorem headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  headRungSubWick_from_three_of_awaySupBound ψ G (QRset χ) D hC'7
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCC hS hCert hNum)

/-- Exact-numerator QR Weil certificates, with bridge-budget nonnegativity discharged from
`A ≥ 0`, supply every head rung from depth `3` onward. -/
theorem headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  headRungSubWick_from_three_of_awaySupBound ψ G (QRset χ) D hC'7
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hCC hS hCert hNum)

/-- Larger-numerator QR Weil certificates at public constant `C' ≤ 7` supply every head rung from
depth `3` onward. -/
theorem headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  headRungSubWick_from_three_of_awaySupBound ψ G (QRset χ) D hC'7
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hS hCert hNum)

/-- Larger-numerator QR Weil certificates, with bridge-budget nonnegativity discharged from
`A ≥ 0`, supply every head rung from depth `3` onward. -/
theorem headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S') :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  headRungSubWick_from_three_of_awaySupBound ψ G (QRset χ) D hC'7
    (awaySupBound_qr_of_shiftedLegendreSupBound_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hCC hS hCert hNum)

end ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers.headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers.headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers.headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const
#print axioms
  ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers.headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
