/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.AgreementGram
import ArkLib.Research.ProximityGap.Frontier.CenteredAgreement
import Mathlib.Tactic.Linarith

/-! # A quadratic bound for lists with bounded pairwise agreement

The polynomial `(z - U) * (z + B)` is nonpositive throughout the interval
of off-diagonal inner products. Summing it over the Gram matrix gives a
list bound even for some positive upper endpoints `U`.
-/

namespace ProximityGap.AgreementQuadratic

open Finset

variable {I J : Type*}

/-- A finite real vector family with constant squared norm and bounded off-diagonal products. -/
theorem gram_bound (S : Finset J) (X : Finset I) (v : J → I → ℝ) (V U B : ℝ)
    (hnorm : ∀ i ∈ S, ∑ x ∈ X, (v i x)^2 = V)
    (hoff : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      -B ≤ ∑ x ∈ X, v i x * v j x ∧ ∑ x ∈ X, v i x * v j x ≤ U)
    (hlinear : U ≤ B) (hdiag : U ≤ V) (hlo : 0 ≤ V + B) :
    (S.card : ℝ) * (V^2 - X.card * U * B) ≤ X.card * (V-U) * (V+B) := by
  classical
  let D (i j : J) := ∑ x ∈ X, v i x * v j x
  let cap := (V-U)*(V+B)
  have hn : 0 ≤ (X.card : ℝ) := Nat.cast_nonneg _
  obtain hempty | hne := S.eq_empty_or_nonempty
  · simp only [hempty, card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (mul_nonneg hn (sub_nonneg.mpr hdiag)) hlo
  have hL : 0 < (S.card : ℝ) := by exact_mod_cast hne.card_pos
  have entry (i : J) (hi : i ∈ S) (j : J) (hj : j ∈ S) :
      D i j ^ 2 ≤ (if i = j then cap else 0) + U*B - (B-U)*D i j := by
    by_cases h : i = j
    · subst j
      have heq : D i i = V := by simpa only [D, ← sq] using hnorm i hi
      rw [heq, ite_eq_left rfl]
      dsimp [cap]
      linarith only [show V^2 = (V-U)*(V+B) + U*B - (B-U)*V by ring]
    · rw [ite_eq_right h, zero_add]
      obtain ⟨lower, upper⟩ := hoff i hi j hj h
      change -B ≤ D i j at lower
      change D i j ≤ U at upper
      nlinarith only [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr upper)
        (show 0 ≤ D i j + B by linarith)]
  have row (i : J) (hi : i ∈ S) :
      ∑ j ∈ S, D i j ^ 2 ≤ cap + S.card * (U*B) - (B-U) * ∑ j ∈ S, D i j := by
    apply (sum_le_sum (entry i hi)).trans_eq
    simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, hi]
  have allRows := sum_le_sum row
  have expand : (∑ i ∈ S, (cap + S.card * (U*B) - (B-U) * ∑ j ∈ S, D i j)) =
      S.card * cap + (S.card : ℝ)^2 * (U*B) - (B-U) * ∑ i ∈ S, ∑ j ∈ S, D i j := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
    ring
  rw [expand] at allRows
  have lin := mul_nonneg (sub_nonneg.mpr hlinear) (AgreementGram.sum_dot_nonneg S X v)
  change 0 ≤ (B-U) * ∑ i ∈ S, ∑ j ∈ S, D i j at lin
  have hsq := AgreementGram.sq_card_mul_sq_norm_le S X v V hnorm
  have total := hsq.trans (mul_le_mul_of_nonneg_left
    (allRows.trans (sub_le_self _ lin)) hn)
  apply le_of_mul_le_mul_left (a := (S.card : ℝ)) _ hL
  calc
    _ = (S.card : ℝ)^2 * V^2 - X.card * (S.card : ℝ)^2 * (U*B) := by ring
    _ ≤ _ := sub_le_sub_right total _
    _ = _ := by dsimp [cap]; ring

/-- Diagonal value of the centered intersection matrix. -/
abbrev variance (n t : ℝ) := t * (n - t)

/-- Upper off-diagonal value from an intersection bound of r sites. -/
abbrev overlap (n t r : ℝ) := n * r - t^2

/-- The quadratic inequality on constant-weight subsets, including the range
where the upper off-diagonal value is positive. -/
theorem constant_weight_bound [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Finset J) (A : J → Finset I) (t r : ℕ)
    (hweight : ∀ i ∈ S, (A i).card = t)
    (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ((A i) ∩ (A j)).card ≤ r)
    (hrt : r ≤ t)
    (hlinear : overlap (Fintype.card I) t r ≤ (t : ℝ)^2) :
    (S.card : ℝ) * (variance (Fintype.card I) t ^ 2 -
      Fintype.card I * overlap (Fintype.card I) t r * (t : ℝ)^2) ≤
      Fintype.card I * (variance (Fintype.card I) t - overlap (Fintype.card I) t r) *
        (variance (Fintype.card I) t + (t : ℝ)^2) := by
  let n : ℝ := Fintype.card I
  have hn : 0 ≤ n := Nat.cast_nonneg _
  let v (i : J) := CenteredAgreement.entry t (A i)
  have diag : ∀ i ∈ S, ∑ x : I, (v i x)^2 = variance n t := by
    intro i hi
    simp only [v, sq]
    rw [CenteredAgreement.dot_eq (A i) (A i) t (hweight i hi) (hweight i hi),
      inter_self, hweight i hi]
    dsimp [variance, n]
    ring
  have off : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      -(t : ℝ)^2 ≤ ∑ x : I, v i x * v j x ∧ ∑ x : I, v i x * v j x ≤ overlap n t r := by
    intro i hi j hj hij
    simp only [v, CenteredAgreement.dot_eq (A i) (A j) t (hweight i hi) (hweight j hj)]
    constructor
    · linarith only [mul_nonneg hn (Nat.cast_nonneg ((A i) ∩ (A j)).card : 0 ≤ (_ : ℝ))]
    · apply sub_le_sub_right _ _
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpair i hi j hj hij) hn
  have hdiag : overlap n t r ≤ variance n t := by
    have hrt' : (r : ℝ) ≤ t := by exact_mod_cast hrt
    dsimp [variance, overlap]
    linarith only [mul_le_mul_of_nonneg_left hrt' hn, mul_comm n (t : ℝ),
      show (t : ℝ)*(n-t) = n*t-t^2 by ring]
  have hlo : 0 ≤ variance n t + (t : ℝ)^2 := by
    rw [show variance n t + (t : ℝ)^2 = n*t by dsimp [variance]; ring]
    exact mul_nonneg hn (Nat.cast_nonneg _)
  simpa only [card_univ] using gram_bound S univ v (variance n t) (overlap n t r)
    ((t : ℝ)^2) diag off hlinear hdiag hlo

#print axioms gram_bound
#print axioms constant_weight_bound
end ProximityGap.AgreementQuadratic
