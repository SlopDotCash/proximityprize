/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R65Deg2SupEquivalence

/-!
# LANE B2 (#466 round 66): budget adapters for the deg-2 sup equivalence

Round 65 exposes the two-sided deg-2 QR/shifted-Legendre sup bridge.  This file adds the
monotonicity and downstream-budget forms, so a future Karatsuba-style bound can be consumed at
any larger incidence budget without reopening the exact Gauss-sum algebra.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters

open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17Deg2WeilRung
open ArkLib.ProximityGap.Frontier.R65Deg2SupEquivalence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {χ : F → ℝ}

/-- Shifted-Legendre sup bounds are monotone in the scalar budget. -/
theorem shiftedLegendreSupBound_mono
    {G : Finset F} {A A' : ℝ}
    (hA : A ≤ A')
    (hW : ShiftedLegendreSupBound χ G A) :
    ShiftedLegendreSupBound χ G A' := by
  intro s hs
  exact (hW s hs).trans hA

/-- Incidence sup bounds are monotone in the scalar budget. -/
theorem incidenceSupBound_mono
    {ψ : AddChar F ℂ} {G H : Finset F} {B B' : ℝ}
    (hB : B ≤ B')
    (hI : IncidenceSupBound ψ G H B) :
    IncidenceSupBound ψ G H B' := by
  intro s hs
  exact (hI s hs).trans hB

/-- Forward deg-2 sup bridge at any larger chosen incidence budget. -/
theorem incidenceSupBound_of_shiftedLegendreSupBound_le
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {A B : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hB : (G.card : ℝ) / 2 + (Real.sqrt (Fintype.card F : ℝ) * A) / 2 ≤ B) :
    IncidenceSupBound ψ G (QRset χ) B :=
  incidenceSupBound_mono hB
    (degTwoIncidenceSupBound_of_shiftedLegendreSupBound hχ hψ G hW)

/-- Converse deg-2 sup bridge at any larger chosen shifted-Legendre budget. -/
theorem shiftedLegendreSupBound_of_incidenceSupBound_le
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {B A : ℝ}
    (hI : IncidenceSupBound ψ G (QRset χ) B)
    (hq1 : 1 ≤ (Fintype.card F : ℝ))
    (hA : (2 * B + (G.card : ℝ)) / Real.sqrt (Fintype.card F : ℝ) ≤ A) :
    ShiftedLegendreSupBound χ G A :=
  shiftedLegendreSupBound_mono hA
    (shiftedLegendreSupBound_of_degTwoIncidenceSupBound hχ hψ G hI hq1)

/-- The forward bridge written with the numerator `(n + sqrt(q) A) / 2`. -/
theorem incidenceSupBound_of_shiftedLegendreSupBound_div_two_le
    (hχ : IsRealQuadChar χ) [DecidablePred fun b : F => χ b = 1]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {A B : ℝ}
    (hW : ShiftedLegendreSupBound χ G A)
    (hB : ((G.card : ℝ) + Real.sqrt (Fintype.card F : ℝ) * A) / 2 ≤ B) :
    IncidenceSupBound ψ G (QRset χ) B := by
  refine incidenceSupBound_of_shiftedLegendreSupBound_le hχ hψ G hW ?_
  linarith

set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters.shiftedLegendreSupBound_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters.incidenceSupBound_mono
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters.incidenceSupBound_of_shiftedLegendreSupBound_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters.shiftedLegendreSupBound_of_incidenceSupBound_le
set_option linter.style.longLine false in
#print axioms
  ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters.incidenceSupBound_of_shiftedLegendreSupBound_div_two_le

end ArkLib.ProximityGap.Frontier.R66Deg2SupBudgetAdapters
