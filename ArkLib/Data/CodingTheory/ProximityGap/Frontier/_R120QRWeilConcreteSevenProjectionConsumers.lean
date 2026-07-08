/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R108QRWeilConcreteClearedScalarSevenPackage

/-!
# LANE B2 (#466 round 120): concrete projection consumers for the constant-seven QR package

R108 packages the concrete denominator-cleared QR/shifted-Legendre certificate as a triple:

* `AwaySupBound`,
* the R19 away tower,
* every head rung from depth `3` onward.

This file exposes direct projections for the concrete and fully-unfolded denominator-cleared
forms, both with bridge-budget nonnegativity supplied directly and with it discharged from `A ≥ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R21HeadRungDichotomy
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R74QRWeilAverageBudgetBridge
open ArkLib.ProximityGap.Frontier.R108QRWeilConcreteClearedScalarSevenPackage

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Concrete denominator-cleared scalar certificates give the QR `AwaySupBound` projection, with
bridge-budget nonnegativity supplied directly. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).1

/-- Concrete denominator-cleared scalar certificates give the R19 away-tower projection, with
bridge-budget nonnegativity supplied directly. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.1

/-- Concrete denominator-cleared scalar certificates give the head-rung-window projection, with
bridge-budget nonnegativity supplied directly. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.2

/-- Concrete denominator-cleared scalar certificates give the QR `AwaySupBound` projection, with
bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).1

/-- Concrete denominator-cleared scalar certificates give the R19 away-tower projection, with
bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.1

/-- Concrete denominator-cleared scalar certificates give the head-rung-window projection, with
bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) * qrWeilSpectralLowerBudget (F := F) G) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.2

/-- Fully-unfolded denominator-cleared scalar certificates give the QR `AwaySupBound`
projection, with bridge-budget nonnegativity supplied directly. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).1

/-- Fully-unfolded denominator-cleared scalar certificates give the R19 away-tower projection,
with bridge-budget nonnegativity supplied directly. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.1

/-- Fully-unfolded denominator-cleared scalar certificates give the head-rung-window projection,
with bridge-budget nonnegativity supplied directly. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hNum).2.2

/-- Fully-unfolded denominator-cleared scalar certificates give the QR `AwaySupBound`
projection, with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem awaySupBound_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    AwaySupBound ψ G (QRset χ) D (7 : ℝ) :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).1

/-- Fully-unfolded denominator-cleared scalar certificates give the R19 away-tower projection,
with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem tower_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ ((7 : ℝ) * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.1

/-- Fully-unfolded denominator-cleared scalar certificates give the head-rung-window projection,
with bridge-budget nonnegativity discharged from `A ≥ 0`. -/
theorem headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} {A : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hNum :
      ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) ^ 2
          * ((QRset χ).card : ℝ)
        ≤ (28 : ℝ) *
          (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2
            - (G.card : ℝ) ^ 2 * Real.sqrt (Fintype.card F)) / 2)) :
    ∀ r : ℕ, 3 ≤ r → HeadRungSubWick ψ G (QRset χ) D r :=
  (awaySupBound_tower_and_headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
    (F := F) (χ := χ) hχ hψ hW hGD hA0 hNum).2.2

end ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_concrete_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.awaySupBound_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.tower_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
#print axioms
  ArkLib.ProximityGap.Frontier.R120QRWeilConcreteSevenProjectionConsumers.headWindow_qr_seven_of_shiftedLegendreSupBound_unfolded_cleared_scalar_of_A_nonneg
