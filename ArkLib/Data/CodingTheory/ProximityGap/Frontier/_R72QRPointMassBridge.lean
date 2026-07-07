/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R72ShiftedLegendreBudgetNonneg

/-!
# LANE B2 (#466 round 72): point-mass witnesses feed the QR spectral budget

Rounds 69--71 reduce the deg-2/Karatsuba tower socket to a QR spectral-mass lower bound

`S <= Σ_{b in QR} ‖η_b‖^2`.

This file adds the point-mass adapter: a single certified QR frequency with
`S <= ‖η_b‖^2` is already enough.  That is the shape produced by max-period witnesses,
level-set certificates, and finite searches, so this bridge lets those inputs feed the
normalized tower budget without redoing sum bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R72QRPointMassBridge

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
open ArkLib.ProximityGap.Frontier.R70ShiftedLegendreMassLowerBridge
open ArkLib.ProximityGap.Frontier.R71ShiftedLegendreBudgetMonotonicity
open ArkLib.ProximityGap.Frontier.R72ShiftedLegendreBudgetNonneg

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A single QR frequency carrying at least `S` spectral mass. -/
def QRPointMassLower
    (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1]
    (ψ : AddChar F ℂ) (G : Finset F) (S : ℝ) : Prop :=
  ∃ b ∈ QRset χ, S ≤ ‖eta ψ G b‖ ^ 2

/-- A member of `QR` contributes at most the total QR spectral mass. -/
theorem qrSpectralMassLower_of_mem
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {b : F}
    (hb : b ∈ QRset χ) :
    ‖eta ψ G b‖ ^ 2 ≤ ∑ c ∈ QRset χ, ‖eta ψ G c‖ ^ 2 :=
  Finset.single_le_sum
    (s := QRset χ) (f := fun c => ‖eta ψ G c‖ ^ 2)
    (fun _ _ => pow_nonneg (norm_nonneg _) _) hb

/-- Point-mass lower bounds are QR spectral-mass lower bounds. -/
theorem qrSpectralMassLower_of_pointMass
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {S : ℝ}
    (hPoint : QRPointMassLower χ ψ G S) :
    QRSpectralMassLower χ ψ G S := by
  rcases hPoint with ⟨b, hb, hS⟩
  exact hS.trans (qrSpectralMassLower_of_mem (F := F) (χ := χ) (ψ := ψ) (G := G) hb)

/-- A point-mass QR lower bound converts a numerator estimate into the exact R69 budget. -/
theorem shiftedLegendreTowerBudget_of_pointMass
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_massLower
    (F := F) (χ := χ) hB0 hC0 (qrSpectralMassLower_of_pointMass hPoint) hNum

/-- Direct all-rung consumer from a shifted-Legendre sup bound and one large QR frequency. -/
theorem tower_qr_of_shiftedLegendreSupBound_pointMass
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreTowerBudget
    (F := F) (χ := χ) hχ hψ hW hGD hC0
    (shiftedLegendreTowerBudget_of_pointMass
      (F := F) (χ := χ) hB0 hC0 hPoint hNum)

/-- Version allowing the final tower constant to be increased after the point-mass estimate. -/
theorem tower_qr_of_shiftedLegendreSupBound_pointMass_le_const
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ shiftedLegendreIncidenceBudget (F := F) G A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_massLower_le_const
    (F := F) (χ := χ) hχ hψ hW hGD hB0 hC0 hC'0 hCC
    (qrSpectralMassLower_of_pointMass hPoint) hNum

/-- A point-mass QR lower bound converts a numerator estimate into the exact R69 budget, with
bridge-budget nonnegativity discharged from `A >= 0`. -/
theorem shiftedLegendreTowerBudget_of_pointMass_of_A_nonneg
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C S : ℝ}
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C :=
  shiftedLegendreTowerBudget_of_pointMass
    (F := F) (χ := χ) (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hPoint hNum

/-- Direct all-rung consumer from one large QR frequency, with bridge-budget nonnegativity
discharged from `A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_pointMass_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0) hC0 hPoint hNum

/-- Larger-final-constant point-mass consumer, with bridge-budget nonnegativity discharged from
`A >= 0`. -/
theorem tower_qr_of_shiftedLegendreSupBound_pointMass_le_const_of_A_nonneg
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' S : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hA0 : 0 ≤ A)
    (hC0 : 0 ≤ C)
    (hC'0 : 0 ≤ C')
    (hCC : C ≤ C')
    (hPoint : QRPointMassLower χ ψ G S)
    (hNum : shiftedLegendreIncidenceBudget (F := F) G A ^ 2 ≤ C * S) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_pointMass_le_const
    (F := F) (χ := χ) hχ hψ hW hGD
    (shiftedLegendreIncidenceBudget_nonneg (F := F) G hA0)
    hC0 hC'0 hCC hPoint hNum

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.qrSpectralMassLower_of_mem
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.qrSpectralMassLower_of_pointMass
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.shiftedLegendreTowerBudget_of_pointMass
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.tower_qr_of_shiftedLegendreSupBound_pointMass
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.tower_qr_of_shiftedLegendreSupBound_pointMass_le_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.shiftedLegendreTowerBudget_of_pointMass_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.tower_qr_of_shiftedLegendreSupBound_pointMass_of_A_nonneg
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R72QRPointMassBridge.tower_qr_of_shiftedLegendreSupBound_pointMass_le_const_of_A_nonneg

end ArkLib.ProximityGap.Frontier.R72QRPointMassBridge
