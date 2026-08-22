/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19RungRecursion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R66Deg2SupBudgetAdapters

/-!
# LANE B2 (#466 round 67): deg-2 sup bounds feed the away tower

Rounds 65--66 package the deg-2 QR face as a two-sided shifted-Legendre/incidence sup problem.
Round 19's recursion consumes the same phenomenon through `AwaySupBound`, where the scalar budget
is measured against the spectral mass `Σ = ∑ b∈H, ‖η_b‖²`.  This file provides the adapter:
an off-diagonal incidence sup bound whose square is at most `C·Σ` yields `AwaySupBound C`, and
therefore plugs into the rung tower.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R19RungRecursion
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence
open ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- R19's tower-local incidence sum is definitionally the same signed incidence field as R15's
incidence sum used by the deg-2 bridge. -/
theorem incidenceSum_r19_eq_r15
    (ψ : AddChar F ℂ) (G H : Finset F) (s : F) :
    R19RungRecursion.incidenceSum ψ G H s
      = R15IncidenceMomentInterchange.incidenceSum ψ G H s := by
  rfl

/-- A direct incidence sup bound implies R19's `AwaySupBound` once the deleted set contains `G`
and the scalar budget is normalized against the spectral mass `Σ`. -/
theorem awaySupBound_of_incidenceSupBound_sq_le
    {ψ : AddChar F ℂ} {G H D : Finset F} {B C : ℝ}
    (hI : IncidenceSupBound ψ G H B)
    (hGD : G ⊆ D)
    (_hB0 : 0 ≤ B)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ H, ‖eta ψ G b‖ ^ 2) :
    AwaySupBound ψ G H D C := by
  intro s hs
  have hsD : s ∉ D := (Finset.mem_sdiff.mp hs).2
  have hsG : s ∉ G := fun hsg => hsD (hGD hsg)
  have hnorm := hI s hsG
  have hnorm' :
      ‖R19RungRecursion.incidenceSum ψ G H s‖ ≤ B := by
    rwa [incidenceSum_r19_eq_r15]
  have hpow : ‖R19RungRecursion.incidenceSum ψ G H s‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm' 2
  exact hpow.trans hBsq

/-- Deg-2 QR version: an incidence sup bound for `QRset χ` feeds `AwaySupBound`. -/
theorem awaySupBound_qr_of_incidenceSupBound_sq_le
    [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} {G D : Finset F} {B C : ℝ}
    (hI : IncidenceSupBound ψ G (QRset χ) B)
    (hGD : G ⊆ D)
    (hB0 : 0 ≤ B)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) :
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_of_incidenceSupBound_sq_le
    (F := F) (ψ := ψ) (G := G) (H := QRset χ) (D := D) (B := B) (C := C)
    hI hGD hB0 hBsq

/-- A shifted-Legendre sup bound feeds the QR away tower at any scalar incidence budget `B`
larger than the exact deg-2 bridge budget, provided `B² ≤ C·Σ`. -/
theorem awaySupBound_qr_of_shiftedLegendreSupBound
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G D : Finset F} {A B C : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hGD : G ⊆ D)
    (hB : (G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2 ≤ B)
    (hB0 : 0 ≤ B)
    (hBsq : B ^ 2 ≤ C * ∑ b ∈ QRset χ, ‖eta ψ G b‖ ^ 2) :
    AwaySupBound ψ G (QRset χ) D C :=
  awaySupBound_qr_of_incidenceSupBound_sq_le
    (F := F) (χ := χ) (ψ := ψ) (G := G) (D := D) (B := B) (C := C)
    (incidenceSupBound_of_shiftedLegendreSupBound_le hχ hψ G hW hB)
    hGD hB0 hBsq

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower.incidenceSum_r19_eq_r15
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower.awaySupBound_of_incidenceSupBound_sq_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower.awaySupBound_qr_of_incidenceSupBound_sq_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower.awaySupBound_qr_of_shiftedLegendreSupBound

end ArkLib.ProximityGap.Frontier.R67Deg2SupToAwayTower
