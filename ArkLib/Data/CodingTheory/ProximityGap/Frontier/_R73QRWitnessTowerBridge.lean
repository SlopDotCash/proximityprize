/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R72QRPointMassBridge

/-!
# LANE B2 (#466 round 73): named QR witnesses feed the shifted-Legendre tower

Round 72 introduced `QRPointMassLower`, an existential wrapper around one large QR frequency.
Most future inputs will name the frequency directly:

`b ∈ QR` and `B(A)^2 <= C * ‖η_b‖^2`.

This file packages that direct witness shape into the R69--R72 tower consumers, including the
common variant where `B(A) >= 0` is discharged from `A >= 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R72QRPointMassBridge
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A named QR witness is a point-mass lower bound at exactly its own mass. -/
theorem qrPointMassLower_of_witness
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {b : F}
    (hb : b ∈ QRset χ) :
    QRPointMassLower χ ψ G (‖eta ψ G b‖ ^ 2) :=
  ⟨b, hb, le_rfl⟩

/-- A named QR witness converts a numerator estimate into the exact R69 budget. -/
theorem shiftedLegendreTowerBudget_of_qrWitness
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C : ℝ} {b : F}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_pointMass
    (F := F) (χ := χ) hB0 hC0 (qrPointMassLower_of_witness hb) hNum

/-- Direct all-rung consumer from a named QR witness. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWitness
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C : ℝ} {b : F}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ c ∈ QRset χ, ‖eta ψ G c‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0
    (qrPointMassLower_of_witness hb) hNum

/-- Larger-final-constant all-rung consumer from a named QR witness. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWitness_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' : ℝ} {b : F}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ c ∈ QRset χ, ‖eta ψ G c‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC
    (qrPointMassLower_of_witness hb) hNum

/-- Named-witness budget with bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem shiftedLegendreTowerBudget_of_qrWitness_of_A_nonneg
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C : ℝ} {b : F}
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_qrWitness
    (F := F) (χ := χ) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hb hNum

/-- Direct named-witness tower consumer with bridge-budget nonnegativity discharged from
`A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWitness_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C : ℝ} {b : F}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ c ∈ QRset χ, ‖eta ψ G c‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_qrWitness
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0) hC0 hb hNum

/-- Larger-final-constant named-witness tower consumer with `B(A) >= 0` from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_qrWitness_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' : ℝ} {b : F}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hb : b ∈ QRset χ)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ c ∈ QRset χ, ‖eta ψ G c‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_qrWitness_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hC'0 hCC hb hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.qrPointMassLower_of_witness
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.shiftedLegendreTowerBudget_of_qrWitness
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.tower_qr_of_shiftedLegendreSupBound_qrWitness
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.tower_qr_of_shiftedLegendreSupBound_qrWitness_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.shiftedLegendreTowerBudget_of_qrWitness_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.tower_qr_of_shiftedLegendreSupBound_qrWitness_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge.tower_qr_of_shiftedLegendreSupBound_qrWitness_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R73QRWitnessTowerBridge
