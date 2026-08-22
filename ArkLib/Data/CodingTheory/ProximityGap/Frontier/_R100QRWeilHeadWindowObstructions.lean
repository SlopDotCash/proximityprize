/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R98QRWeilHeadRungWindowConsumers

/-!
# LANE B2 (#466 round 100): head-rung failures obstruct QR Weil certificates

R98 says that a named QR Weil certificate at public constant `≤ 7` supplies every head rung
from depth `3` onward.  This file records the contrapositive in the same public API shapes:
any actual failure of a head-rung sub-Wick step rules out the corresponding QR certificate data.

This is a certificate-audit tool.  It keeps proposed shifted-Legendre/Paley inputs honest by
making the first downstream obstruction explicit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions

open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R98QRWeilHeadRungWindowConsumers

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- If a head rung at depth `r ≥ 3` fails, then exact-numerator QR Weil certificate data at
public constant `C' ≤ 7` cannot exist. -/
theorem not_qrWeil_certificate_mono_threshold_le_const_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ QRWeilAverageCertificate χ G S N := by
  intro hCert
  exact hfail
    (headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hCC hC'7 hS hCert hNum r hr)

/-- Same obstruction, with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem not_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F}
    {A C C' S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ QRWeilAverageCertificate χ G S N := by
  intro hCert
  exact hfail
    (headRungSubWick_from_three_of_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hC0 hCC hC'7 hS hCert hNum r hr)

/-- If a head rung at depth `r ≥ 3` fails, then larger-numerator QR Weil certificate data at
public constant `C' ≤ 7` cannot exist. -/
theorem not_qrWeil_certificate_le_sq_mono_threshold_le_const_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hNum : B ^ 2 ≤ C * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ QRWeilAverageCertificate χ G S N := by
  intro hCert
  exact hfail
    (headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const
      (F := F) (χ := χ) hχ hψ hW hGD hB0 hB hC0 hCC hC'7 hS hCert hNum r hr)

/-- Same larger-numerator obstruction, with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem not_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg_of_headRung_failure
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S S' N : ℝ} {r : ℕ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hCC : C ≤ C')
    (hC'7 : C' ≤ (7 : ℝ))
    (hS : S' ≤ S)
    (hNum : B ^ 2 ≤ C * S')
    (hr : 3 ≤ r)
    (hfail : ¬ HeadRungSubWick ψ G (QRset χ) D r) :
    ¬ QRWeilAverageCertificate χ G S N := by
  intro hCert
  exact hfail
    (headRungSubWick_from_three_of_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg
      (F := F) (χ := χ) hχ hψ hW hGD hA0 hB hC0 hCC hC'7 hS hCert hNum r hr)

end ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions.not_qrWeil_certificate_mono_threshold_le_const_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions.not_qrWeil_certificate_mono_threshold_le_const_of_A_nonneg_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions.not_qrWeil_certificate_le_sq_mono_threshold_le_const_of_headRung_failure
#print axioms
  ArkLib.ProximityGap.Frontier.R100QRWeilHeadWindowObstructions.not_qrWeil_certificate_le_sq_mono_threshold_le_const_of_A_nonneg_of_headRung_failure
