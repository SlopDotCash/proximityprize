/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R68Deg2SupTowerConsumer

/-!
# LANE B2 (#466 round 69): the normalized shifted-Legendre tower budget

Rounds 65--68 give the exact path

`shifted-Legendre sup` -> `QR incidence sup` -> `AwaySupBound` -> all corrected-B rungs.

This file names the remaining scalar normalization as a single Prop at the exact deg-2 bridge
constant.  A future Karatsuba/Shkredov-style theorem now has a precise socket:

`((|G| + sqrt(q) * A) / 2)^2 <= C * Σ_QR`.

No analytic estimate is proved here; the point is to remove bookkeeping from the next attack.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- The exact incidence budget produced by a shifted-Legendre bound of size `A` on `G`. -/
noncomputable def shiftedLegendreIncidenceBudget (G : Finset F) (A : ℝ) : ℝ :=
  ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2

/-- The normalized scalar condition needed to feed a shifted-Legendre estimate into the R19
away tower at constant `C`.  This is the deg-2/Karatsuba socket. -/
def ShiftedLegendreTowerBudget
    (χ : F → ℝ) [DecidablePred fun b : F => χ b = 1]
    (ψ : AddChar F ℂ) (G : Finset F) (A C : ℝ) : Prop :=
  0 ≤ shiftedLegendreIncidenceBudget (F := F) G A ∧
    shiftedLegendreIncidenceBudget (F := F) G A ^ 2
      ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2

/-- The exact bridge budget written in the form expected by R68. -/
theorem shiftedLegendreIncidenceBudget_spec (G : Finset F) (A : ℝ) :
    ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2
      ≤ shiftedLegendreIncidenceBudget (F := F) G A := by
  rfl

/-- The normalized shifted-Legendre tower budget is monotone in the tower constant. -/
theorem shiftedLegendreTowerBudget_mono_const
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G : Finset F} {A C C' : ℝ}
    (hCC : C ≤ C')
    (hBudget : ShiftedLegendreTowerBudget (χ := χ) ψ G A C) :
    ShiftedLegendreTowerBudget (χ := χ) ψ G A C' := by
  refine ⟨hBudget.1, ?_⟩
  have hsum_nonneg : 0 ≤ ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2 := by
    exact Finset.sum_nonneg (fun b _ => sq_nonneg _)
  exact hBudget.2.trans (mul_le_mul_of_nonneg_right hCC hsum_nonneg)

/-- A shifted-Legendre sup bound plus the named normalized budget feeds every later deg-2 QR
away rung. -/
theorem tower_qr_of_shiftedLegendreTowerBudget
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hC0 : 0 ≤ C)
    (hBudget : ShiftedLegendreTowerBudget (χ := χ) ψ G A C) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound_div_two
    (F := F) (χ := χ) hχ hψ (G := G) (D := D) (A := A)
    (B := shiftedLegendreIncidenceBudget (F := F) G A) (C := C)
    hW hGD (shiftedLegendreIncidenceBudget_spec (F := F) G A) hBudget.1 hC0 hBudget.2

/-- A shifted-Legendre tower budget proved at a sharper constant can be consumed at any larger
tower constant. -/
theorem tower_qr_of_shiftedLegendreTowerBudget_le
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A C C' : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hCC : C ≤ C')
    (hC0 : 0 ≤ C')
    (hBudget : ShiftedLegendreTowerBudget (χ := χ) ψ G A C) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C' * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreTowerBudget hχ hψ hW hGD hC0
    (shiftedLegendreTowerBudget_mono_const (χ := χ) hCC hBudget)

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget.shiftedLegendreIncidenceBudget_spec
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget.shiftedLegendreTowerBudget_mono_const
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget.tower_qr_of_shiftedLegendreTowerBudget
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget.tower_qr_of_shiftedLegendreTowerBudget_le

end ArkLib.ProximityGap.Frontier.R69ShiftedLegendreTowerBudget
