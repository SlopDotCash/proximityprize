/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R67Deg2SupToAwayTower

/-!
# LANE B2 (#466 round 68): deg-2 sup bounds feed the whole away tower

Round 67 turns a deg-2 QR incidence or shifted-Legendre sup estimate into R19's fixed-point
`AwaySupBound`.  R19 already proves that `AwaySupBound` propagates through all later corrected-B
rungs.  This file is the downstream consumer: it exposes the composed tower statement directly,
so the next Karatsuba-style input can plug in without reopening the R19 recursion algebra.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- A QR incidence sup bound whose square is normalized by `C·Σ` feeds every later R19 rung. -/
theorem tower_qr_of_incidenceSupBound_sq_le
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G D : Finset F} {B C : ℝ}
    (hI : IncidenceSupBound ψ G (QRset χ) B)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ C)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_of_awaySupBound ψ G (QRset χ) D hC0
    (awaySupBound_qr_of_incidenceSupBound_sq_le
      (F := F) (χ := χ) (ψ := ψ) (G := G) (D := D) (B := B) (C := C)
      hI hGD hB0 hBsq)

/-- A shifted-Legendre sup bound feeds every later deg-2 QR away rung once its incidence budget
is normalized by `C·Σ`. -/
theorem tower_qr_of_shiftedLegendreSupBound
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB : (G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2 ≤ B)
    (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ C)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_of_awaySupBound ψ G (QRset χ) D hC0
    (awaySupBound_qr_of_shiftedLegendreSupBound
      (F := F) (χ := χ) hχ hψ (G := G) (D := D) (A := A) (B := B) (C := C)
      hW hGD hB hB0 hBsq)

/-- Numerator-over-two version of `tower_qr_of_shiftedLegendreSupBound`. -/
theorem tower_qr_of_shiftedLegendreSupBound_div_two
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB : ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2 ≤ B)
    (hB0 : 0 ≤ B)
    (hC0 : 0 ≤ C)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) :
    ∀ r : ℕ, rungMoment ψ G (QRset χ) D (r + 2)
      ≤ (C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) ^ r
          * rungMoment ψ G (QRset χ) D 2 :=
  tower_qr_of_shiftedLegendreSupBound hχ hψ hW hGD (by linarith) hB0 hC0 hBsq

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer.tower_qr_of_incidenceSupBound_sq_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer.tower_qr_of_shiftedLegendreSupBound
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer.tower_qr_of_shiftedLegendreSupBound_div_two

end ArkLib.ProximityGap.Frontier.R68Deg2SupTowerConsumer
