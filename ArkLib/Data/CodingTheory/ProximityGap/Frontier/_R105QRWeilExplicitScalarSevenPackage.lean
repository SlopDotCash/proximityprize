/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R104QRWeilExactScalarSevenPackage

/-!
# LANE B2 (#466 round 105): explicit scalar constant-seven QR package

R104 reduces the QR/Weil head-rung window to the exact named scalar target

`shiftedLegendreIncidenceBudget G A ^ 2 * #QR ≤ 7*N`.

This file unfolds the incidence budget, exposing the remaining arithmetic target as

`(((|G| + sqrt(q) * A) / 2)^2) * #QR ≤ 7*N`.

No analytic estimate is proved here; this is a final-form consumer for an explicit
shifted-Legendre cancellation certificate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R105QRWeilExplicitScalarSevenPackage

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R104QRWeilExactScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Explicit scalar constant-seven package: the unfolded shifted-Legendre incidence budget pays
the cross-multiplied QR numerator inequality. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_explicit_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum :
      (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar
    (F := F) (χ := χ) hχ hψ hW hGD
    (by simpa [shiftedLegendreIncidenceBudget] using hB0)
    hN
    (by simpa [shiftedLegendreIncidenceBudget] using hNum)

/-- Explicit scalar constant-seven package with bridge-budget nonnegativity discharged from
`A ≥ 0`. -/
theorem awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_explicit_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A N : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hN : N ≤ qrWeilSpectralLowerBudget (F := F) G)
    (hNum :
      (((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (7 : ℝ) * N) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) ∧
      (∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
        ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
            * rungMoment ψ G (QRset χ) D 2) ∧
      (∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r) :=
  awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_exact_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hN
    (by simpa [shiftedLegendreIncidenceBudget] using hNum)

end ArkLib.ProximityGap.Frontier.R105QRWeilExplicitScalarSevenPackage

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R105QRWeilExplicitScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_explicit_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R105QRWeilExplicitScalarSevenPackage.awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_explicit_scalar_of_A_nonneg
