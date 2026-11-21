/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._ThirdMomentUpperLineCap
import ArkLib.Research.ProximityGap.Frontier._ThirdMomentJensenGeneral

/-!
# A large polynomial line is forced at the production rate-sixteenth parameters

After at most one line is removed, at least 503316482 points remain. If all remaining
cores have fewer than the agreement threshold minus 1/660 of the length, their line
occupancies satisfy the relative bound in the theorem below. The cubic incidence
lower bound contradicts that bound, even at the smallest admitted agreement threshold.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators
open ArkLib.ProximityGap.Frontier.HalfPredecessorThirdMomentUpper
open ArkLib.ProximityGap.Frontier.ThirdMomentUpperLineCap
open ArkLib.ProximityGap.Frontier.ThirdMomentJensenGeneral

namespace ArkLib.ProximityGap.Frontier.TwoCoreMomentForcing

/-- The three factors in the exact Jensen cubic each dominate a fixed multiple of
the point count. The two units lost in the last factor are covered at the minimum count. -/
private theorem production_cubic_gap (m : ℚ) (hm : 503316482 ≤ m) :
    let a := m * 426115517 / 1073741824
    67109214 * m ^ 3 < 1073741824 * a * (a - 1) * (a - 2) := by
  let r : ℚ := 39685099 / 100000000
  let a : ℚ := m * 426115517 / 1073741824
  change 67109214 * m ^ 3 < 1073741824 * a * (a - 1) * (a - 2)
  have hmpos : 0 < m := by linarith
  have hr : 0 < r := by norm_num [r]
  have hscale : (67109214 : ℚ) < 1073741824 * r ^ 3 := by norm_num [r]
  have hlast : r * m ≤ a - 2 := by dsimp [a, r]; linarith
  have hfirst : r * m ≤ a := by linarith
  have hsecond : r * m ≤ a - 1 := by linarith
  have hnonneg : 0 ≤ r * m := mul_nonneg hr.le hmpos.le
  have ha0 : 0 ≤ a := hnonneg.trans hfirst
  have ha1 : 0 ≤ a - 1 := hnonneg.trans hsecond
  calc
    67109214 * m ^ 3 < (1073741824 * r ^ 3) * m ^ 3 :=
      mul_lt_mul_of_pos_right hscale (pow_pos hmpos 3)
    _ = 1073741824 * (r * m) * (r * m) * (r * m) := by ring
    _ ≤ 1073741824 * a * (a - 1) * (a - 2) := by gcongr

private theorem scale_to_weight (u v : ℕ) (h : 1073741824 * u ≤ 660 * v) :
    u * 570425344 ≤ 351 * v := by
  have hh : 1073741824 * (u : ℚ) ≤ 660 * (v : ℚ) := by exact_mod_cast h
  have hpos : 0 ≤ (v : ℚ) := by positivity
  have hh' : (u : ℚ) * 570425344 ≤ 351 * (v : ℚ) := by linarith
  exact_mod_cast hh'

/-- A subfamily at the production agreement threshold cannot have small line occupancy
and the stated collinear and noncollinear triple bounds simultaneously.

The line-cap hypothesis has its scale expressed directly against the subfamily's
cardinality, so no rounding or assumption that the exceptional line is occupied is needed. -/
theorem production_small_lines_impossible
    {U Point Line : Type*} [Fintype U] [DecidableEq U]
    (G : Finset Point) (A : Point → Finset U) (onLine : Line → Point → Prop)
    (determinedLine : Point → Point → Line) (t B : ℕ)
    (hn : Fintype.card U = 1073741824)
    (hM : 503316482 ≤ G.card) (htlo : 426115517 ≤ t) (hthi : t ≤ 570425344)
    (hrich : ∀ x ∈ G, t ≤ (A x).card)
    (hscale : 1073741824 * (B - 2) ≤ 660 * (G.card - 2))
    (hpairOn : ∀ x ∈ G, ∀ y ∈ G, x ≠ y →
      onLine (determinedLine x y) x ∧ onLine (determinedLine x y) y)
    (hpairUnique : ∀ ell x y, x ≠ y → onLine ell x → onLine ell y →
      ell = determinedLine x y)
    (hline : ∀ ell, (linePoints G onLine ell).card ≤ B)
    (hnoncol : ∀ T ∈ G.powersetCard 3, ¬ Collinear onLine T →
      (commonCoordinates A T).card ≤ 67108863)
    (hcol : ∀ T ∈ collinearTriples G onLine, (commonCoordinates A T).card ≤ t) : False := by
  classical
  let mult (i : U) := (G.filter fun x => i ∈ A x).card
  have hsum : ∑ i, mult i = ∑ x ∈ G, (A x).card := by
    simp only [mult, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hinc : G.card * 426115517 ≤ ∑ i, mult i := by
    rw [hsum]
    calc
      G.card * 426115517 = ∑ _x ∈ G, 426115517 := by simp
      _ ≤ ∑ x ∈ G, (A x).card := Finset.sum_le_sum fun x hx => htlo.trans (hrich x hx)
  have hjensen := thirdMoment_jensen_lower_rat_general mult 1073741824 G.card 426115517
    (by decide) hn ((show 2 * 1073741824 ≤ 503316482 * 426115517 by norm_num).trans
      (Nat.mul_le_mul_right _ hM)) hinc
  have hupper := weightedTripleSum_upper_lineCap G onLine determinedLine
    (fun T => (commonCoordinates A T).card) 67108863 t B
    hpairOn hpairUnique hline hnoncol (fun T hT => by have := hcol T hT; omega)
  rw [← sum_choose_incidence_eq_sum_commonCoordinates_card G A] at hupper
  have hx : (B - 2) * t ≤ 351 * (G.card - 2) := by
    calc
      (B - 2) * t ≤ (B - 2) * 570425344 := Nat.mul_le_mul_left _ hthi
      _ ≤ 351 * (G.card - 2) := scale_to_weight _ _ hscale
  have hupper' : 6 * ∑ i, (mult i).choose 3 ≤ 67109214 * G.card ^ 3 := by
    refine hupper.trans ?_
    calc
      _ ≤ 67108863 * G.card * (G.card - 1) * (G.card - 2) +
          (351 * (G.card - 2)) * G.card * (G.card - 1) := by gcongr
      _ = 67109214 * G.card * (G.card - 1) * (G.card - 2) := by ring
      _ ≤ 67109214 * G.card * G.card * G.card := by gcongr <;> omega
      _ = _ := by ring
  have hcast : 6 * ∑ i, ((mult i).choose 3 : ℚ) ≤ 67109214 * (G.card : ℚ) ^ 3 := by
    exact_mod_cast hupper'
  have hgap := production_cubic_gap (G.card : ℚ) (by exact_mod_cast hM)
  exact (not_lt_of_ge (hjensen.trans hcast)) hgap

end ArkLib.ProximityGap.Frontier.TwoCoreMomentForcing

#print axioms ArkLib.ProximityGap.Frontier.TwoCoreMomentForcing.production_small_lines_impossible
