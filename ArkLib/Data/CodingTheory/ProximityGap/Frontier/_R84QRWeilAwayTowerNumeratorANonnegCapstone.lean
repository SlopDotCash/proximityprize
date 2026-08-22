/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R83QRWeilAwayTowerNumeratorCapstone

/-!
# LANE B2 (#466 round 84): `A >= 0` larger-numerator away-tower capstones

Round 83 added fixed-point plus tower capstones for larger-numerator QR Weil certificates, but
those consumers still asked directly for nonnegativity of the exact shifted-Legendre bridge budget.
This file provides the analytic-facing variants where that nonnegativity is discharged from the
more natural hypothesis `A >= 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R84QRWeilAwayTowerNumeratorANonnegCapstone

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R75QRWeilBudgetCertificate
open ArkLib.ProximityGap.Frontier.R83QRWeilAwayTowerNumeratorCapstone

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR Weil certificate with a larger numerator `B` gives the relaxed fixed-point
`AwaySupBound` and all later R19 away rungs, with bridge-budget nonnegativity discharged from
`A >= 0`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hCert : QRWeilAverageCertificate χ G S N)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hB hC0 hC'0 hCC hCert hNum

/-- Normalized QR Weil data with a larger numerator gives the relaxed fixed-point `AwaySupBound`
and all later R19 away rungs, with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A B C C' S N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hB : shiftedLegendreIncidenceBudget (F := F) G A ≤ B)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hS : S ≤ N / ((QRset χ).card : ℝ))
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum : B ^ 2 ≤ C * S) :
    AwaySupBound ψ G (QRset χ) D C' ∧
      ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2 :=
  awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hB hC0 hC'0 hCC hS hN hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R84QRWeilAwayTowerNumeratorANonnegCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_certificate_le_sq_le_const_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R84QRWeilAwayTowerNumeratorANonnegCapstone.awaySupBound_and_tower_qr_of_shiftedLegendreSupBound_le_div_le_sq_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R84QRWeilAwayTowerNumeratorANonnegCapstone
