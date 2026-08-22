/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DilationRealSignCocycle
import Mathlib.Tactic.Linarith

/-!
# Door-IV sign-cocycle mass balance (#444)

`DilationRealSignCocycle` proved the structural door-(iv) identity

`∑ b, (η_b(G)).re * (η_{ζ b}(G)).re = 0`.

This file packages the exact finite consequence the proof narrative uses: the positive same-sign
(doubling) cross-mass equals the negative opposite-sign (cancelling) cross-mass. Thus a sign-cocycle
argument cannot keep only the doubling side: every positive-weight same-sign budget must be paid for by
an equal opposite-sign budget. This is a constraint lemma, not a CORE bound.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false


namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

open scoped BigOperators
open Finset

variable {ι : Type*} [Fintype ι]

/-- Positive part of a real number, written with `max` to avoid extra dependencies. -/
def posPart (x : ℝ) : ℝ := max x 0

/-- Negative part magnitude of a real number, written with `max (-x) 0`. -/
def negPart (x : ℝ) : ℝ := max (-x) 0

lemma real_eq_posPart_sub_negPart (x : ℝ) :
    x = posPart x - negPart x := by
  unfold posPart negPart
  by_cases hx : 0 ≤ x
  · have hmx : max x 0 = x := max_eq_left hx
    have hmneg : max (-x) 0 = 0 := max_eq_right (by linarith)
    rw [hmx, hmneg]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hmx : max x 0 = 0 := max_eq_right hxle
    have hmneg : max (-x) 0 = -x := max_eq_left (by linarith)
    rw [hmx, hmneg]
    ring

/-- If a finite real spectrum has total sum zero, its positive mass equals its negative mass. -/
theorem posMass_eq_negMass_of_sum_zero (a : ι → ℝ) (hzero : ∑ i, a i = 0) :
    ∑ i, posPart (a i) = ∑ i, negPart (a i) := by
  have hdecomp : ∑ i, a i = (∑ i, posPart (a i)) - ∑ i, negPart (a i) := by
    calc
      ∑ i, a i = ∑ i, (posPart (a i) - negPart (a i)) := by
        exact Finset.sum_congr rfl (fun i _ => real_eq_posPart_sub_negPart (a i))
      _ = (∑ i, posPart (a i)) - ∑ i, negPart (a i) := by
        rw [Finset.sum_sub_distrib]
  linarith

/-- The positive sign-cross mass is nonnegative. -/
lemma posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  unfold posPart
  exact le_max_right x 0

/-- The negative sign-cross mass is nonnegative. -/
lemma negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  unfold negPart
  exact le_max_right (-x) 0

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Door-IV sign-cocycle mass balance.** For a negation-closed child set `G` and a disjoint dilate,
the positive same-sign cross-products and the negative opposite-sign cross-products have exactly the same
mass over all frequencies. The doubling branch is therefore globally budget-balanced by the cancellation
branch; a proof may still need a worst-frequency sign-word theorem, but it cannot obtain mass from the
`+` side without paying the `-` side. -/
theorem sign_positiveMass_eq_negativeMass {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      ∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re) := by
  exact posMass_eq_negMass_of_sum_zero
    (fun b : F => (eta ψ G b).re * (eta ψ G (ζ * b)).re)
    (sign_balance_zero hψ G hG hdisj)

/-- If all sign-cross products are nonnegative, sign balance forces every positive part to have zero
sum. This is the finite obstruction to a globally all-`+` sign cocycle with positive mass. -/
theorem positiveMass_zero_of_all_nonneg {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G))
    (hall : ∀ b : F, 0 ≤ (eta ψ G b).re * (eta ψ G (ζ * b)).re) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) = 0 := by
  have hnegzero : (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) = 0 := by
    refine Finset.sum_eq_zero (fun b _ => ?_)
    unfold negPart
    rw [max_eq_right]
    linarith [hall b]
  rw [sign_positiveMass_eq_negativeMass hψ G hG hdisj, hnegzero]

/-- Nonzero positive sign-cross mass rules out a globally nonnegative sign cocycle. Equivalently, any
nontrivial same-sign mass forces at least one cancelling/opposite-sign contribution somewhere else. -/
theorem not_all_nonneg_of_positiveMass_pos {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G))
    (hpos : 0 < ∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) :
    ¬ ∀ b : F, 0 ≤ (eta ψ G b).re * (eta ψ G (ζ * b)).re := by
  intro hall
  have hzero := positiveMass_zero_of_all_nonneg hψ G hG hdisj hall
  linarith

/-- Local witness form of the sign-cocycle obstruction: if the same-sign/doubling branch has positive
mass, then some frequency has an actually negative sign-cross product. This rules out interpreting the
balance theorem as merely abstract cancellation of totals: nonzero positive alignment forces a concrete
opposite-sign frequency in the same finite spectrum. -/
theorem exists_negative_cross_of_positiveMass_pos {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (dilate ζ G))
    (hpos : 0 < ∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) :
    ∃ b : F, (eta ψ G b).re * (eta ψ G (ζ * b)).re < 0 := by
  have hnot := not_all_nonneg_of_positiveMass_pos hψ G hG hdisj hpos
  push_neg at hnot
  exact hnot

/-- Symmetric local witness: if the cancelling/opposite-sign branch has positive mass, then some
frequency has an actually positive sign-cross product. Together with
`exists_negative_cross_of_positiveMass_pos`, the exact sign-cocycle balance is witnessed on both sides
of the finite spectrum rather than only as a global equality of totals. -/
theorem exists_positive_cross_of_negativeMass_pos {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (dilate ζ G))
    (hneg : 0 < ∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) :
    ∃ b : F, 0 < (eta ψ G b).re * (eta ψ G (ζ * b)).re := by
  by_contra hnone
  push_neg at hnone
  have hposzero : (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) = 0 := by
    refine Finset.sum_eq_zero (fun b _ => ?_)
    unfold posPart
    rw [max_eq_right]
    exact hnone b
  have hPN := sign_positiveMass_eq_negativeMass hψ G hG hdisj
  linarith

lemma posPart_add_negPart_eq_abs (x : ℝ) : posPart x + negPart x = |x| := by
  unfold posPart negPart
  by_cases hx : 0 ≤ x
  · have hmx : max x 0 = x := max_eq_left hx
    have hmneg : max (-x) 0 = 0 := max_eq_right (by linarith)
    rw [hmx, hmneg, abs_of_nonneg hx]
    ring
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hmx : max x 0 = 0 := max_eq_right hxle
    have hmneg : max (-x) 0 = -x := max_eq_left (by linarith)
    rw [hmx, hmneg, abs_of_nonpos hxle]
    ring

/-- The total positive-plus-negative sign-cross mass is the total norm cross-mass. Reality of the
negation-closed child periods turns `|Re η_b · Re η_{ζb}|` into `‖η_b‖‖η_{ζb}‖`. -/
theorem sign_totalParts_eq_total_doublingMass {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) (ζ : F) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) +
        (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      ∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖ := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [posPart_add_negPart_eq_abs, norm_eta_eq_abs_re G hG b, norm_eta_eq_abs_re G hG (ζ * b), abs_mul]

/-- **Half-budget corollary.** The same-sign/doubling mass is at most half of the total Cauchy--Schwarz
cross budget, hence at most `q·|G|/2`. This formalizes the narrative consequence of
`sign_balance_zero` plus `total_doublingMass_le`: positive alignment mass is globally capped by an equal
cancellation mass and cannot occupy the whole L² budget. -/
theorem positiveMass_le_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 := by
  set P := ∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re) with hP
  set N := ∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re) with hN
  set C := (Fintype.card F : ℝ) * G.card with hC
  have hPN : P = N := by
    rw [hP, hN]
    exact sign_positiveMass_eq_negativeMass hψ G hG hdisj
  have htotal : P + N ≤ C := by
    rw [hP, hN, hC, sign_totalParts_eq_total_doublingMass G hG ζ]
    exact total_doublingMass_le hψ G hζ
  linarith

/-- The cancelling/opposite-sign mass obeys the same half-budget cap as the positive same-sign mass.
Together with `positiveMass_le_half_card`, this records that neither side of the sign cocycle can
occupy more than half of the Cauchy--Schwarz cross budget. -/
theorem negativeMass_le_half_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 := by
  rw [← sign_positiveMass_eq_negativeMass hψ G hG hdisj]
  exact positiveMass_le_half_card hψ G hG hζ hdisj

/-- Exact half-splitting form of the sign-cocycle balance: under the door-IV disjoint-dilate
hypotheses, the positive same-sign mass is exactly one half of the total positive-plus-negative mass. -/
theorem positiveMass_eq_half_totalParts {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      ((∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) +
        ∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) / 2 := by
  have hPN := sign_positiveMass_eq_negativeMass hψ G hG hdisj
  linarith

/-- Exact half-splitting form for the cancelling/opposite-sign mass. The sign-cocycle budget is split
evenly between the same-sign and opposite-sign branches. -/
theorem negativeMass_eq_half_totalParts {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      ((∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) +
        ∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) / 2 := by
  have hPN := sign_positiveMass_eq_negativeMass hψ G hG hdisj
  linarith

/-- The total sign-cross mass itself is bounded by the Cauchy--Schwarz budget `q·|G|`. -/
theorem totalParts_le_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) +
        (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) ≤
      (Fintype.card F : ℝ) * G.card := by
  rw [sign_totalParts_eq_total_doublingMass G hG ζ]
  exact total_doublingMass_le hψ G hζ

/-- Direct norm-cross form of the exact split: the same-sign/doubling mass is exactly half of the
total `‖η_b‖‖η_ζb‖` cross mass. This is the citable version used when the sign-cocycle budget is
compared directly to the Cauchy--Schwarz cross term. -/
theorem positiveMass_eq_half_total_doublingMass {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, posPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      (∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖) / 2 := by
  rw [positiveMass_eq_half_totalParts hψ G hG hdisj, sign_totalParts_eq_total_doublingMass G hG ζ]

/-- Direct norm-cross form for the cancelling branch: opposite-sign mass is also exactly half of the
total `‖η_b‖‖η_ζb‖` cross mass. -/
theorem negativeMass_eq_half_total_doublingMass {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hdisj : Disjoint G (dilate ζ G)) :
    (∑ b : F, negPart ((eta ψ G b).re * (eta ψ G (ζ * b)).re)) =
      (∑ b : F, ‖eta ψ G b‖ * ‖eta ψ G (ζ * b)‖) / 2 := by
  rw [negativeMass_eq_half_totalParts hψ G hG hdisj, sign_totalParts_eq_total_doublingMass G hG ζ]

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posMass_eq_negMass_of_sum_zero
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sign_positiveMass_eq_negativeMass
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_zero_of_all_nonneg
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.not_all_nonneg_of_positiveMass_pos
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_negative_cross_of_positiveMass_pos
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_positive_cross_of_negativeMass_pos
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sign_totalParts_eq_total_doublingMass
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_le_half_card
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_le_half_card
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_eq_half_totalParts
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_eq_half_totalParts
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.totalParts_le_card
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_eq_half_total_doublingMass
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_eq_half_total_doublingMass
