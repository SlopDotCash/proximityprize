/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Fourth moments of agreement-support intersection deficits

These finite sum inequalities give the spectral upper estimate and the nonnegative
entry lower estimate used in the written all-center list bound. -/

namespace ProximityGap.SupportDeficitFourthMoment

open Finset

variable {ι : Type*} [Fintype ι]

/-- Unit eigenvalues occupying at least half the spectrum and zero trace force
the second moment to be at least the matrix size. -/
theorem secondMoment_ge_size (u : ℕ) (e : ι → ℝ)
    (hcard : Fintype.card ι ≤ u) (htrace : (u : ℝ) + ∑ i, e i = 0) :
    (u : ℝ) + Fintype.card ι ≤ u + ∑ i, e i ^ 2 := by
  have hsq : 0 ≤ ∑ i, (e i ^ 2 + (2 * e i + 1)) :=
    sum_nonneg fun i _ => by nlinarith [sq_nonneg (e i + 1)]
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsq
  have hc : (Fintype.card ι : ℝ) ≤ u := by exact_mod_cast hcard
  linarith

/-- The cubic trace estimate bounds the fourth moment away from the unit spectrum. -/
theorem spectralFourthUpper (r : ℝ) (e : ι → ℝ) (hr : 1 ≤ r)
    (hlo : ∀ i, -r ≤ e i) (hhi : ∀ i, e i ≤ 1)
    (hcubic : ∑ i, (1 - e i) * (e i + 1) ^ 2 ≤ (r - 1) * (r + 1) ^ 2) :
    (r^2 - 1)^2 + ∑ i, (e i ^ 2 - 1)^2 ≤ 2 * r * (r - 1) * (r + 1)^2 := by
  have hterm (i : ι) : (e i ^ 2 - 1)^2 ≤
      (r + 1) * ((1 - e i) * (e i + 1)^2) := by
    calc
      _ = (1 - e i) * ((1 - e i) * (e i + 1)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [hlo i])
        (mul_nonneg (sub_nonneg.mpr (hhi i)) (sq_nonneg _))
  have hs := sum_le_sum (s := (univ : Finset ι)) fun i _ => hterm i
  rw [← mul_sum] at hs
  have hmul := mul_le_mul_of_nonneg_left hcubic (show 0 ≤ r + 1 by linarith)
  calc
    _ ≤ (r^2 - 1)^2 + (r + 1) * ((r - 1) * (r + 1)^2) := by linarith
    _ = _ := by ring

/-- The entrywise lower bound for the fourth trace of a nonnegative symmetric matrix.
The repeated-index correction keeps exactly the two ways to return in four steps. -/
theorem entryFourthLower (w : ι → ι → ℝ) (hsym : ∀ i j, w i j = w j i)
    (hpos : ∀ i j, 0 ≤ w i j) :
    2 * ∑ i, (∑ k, w i k ^ 2)^2 - (∑ i, ∑ k, w i k ^ 4) ≤
      ∑ i, ∑ j, (∑ k, w i k * w j k)^2 := by
  classical
  have each (i j : ι) :
      (∑ k, w i k ^ 2 * w j k ^ 2) +
        (if i = j then (∑ k, w i k ^ 2)^2 - (∑ k, w i k ^ 4) else 0) ≤
        (∑ k, w i k * w j k)^2 := by
    by_cases heq : i = j
    · subst j
      simp only [ite_true, ← sq, ← pow_mul]
      norm_num
    · simp only [ite_eq_right heq, add_zero]
      simpa only [mul_pow] using (sum_sq_le_sq_sum_of_nonneg (s := (univ : Finset ι))
        (f := fun k => w i k * w j k) (fun k _ => mul_nonneg (hpos i k) (hpos j k)))
  have repeated : (∑ i, ∑ j, ∑ k, w i k ^ 2 * w j k ^ 2) =
      ∑ k, (∑ i, w k i ^ 2)^2 := by
    calc
      _ = ∑ i, ∑ k, ∑ j, w i k ^ 2 * w j k ^ 2 :=
        sum_congr rfl fun i _ => sum_comm
      _ = ∑ k, ∑ i, ∑ j, w i k ^ 2 * w j k ^ 2 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro k _
        simp only [← mul_sum, ← sum_mul, pow_two]
        congr 1 <;> apply sum_congr rfl <;> intro i _ <;> rw [hsym i k]
  have h := sum_le_sum (s := (univ : Finset ι)) fun i _ =>
    sum_le_sum (s := (univ : Finset ι)) fun j _ => each i j
  simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, sum_sub_distrib] at h
  linarith [repeated]

/-- The finite rational comparison used by the production endpoint certificates. -/
def fourthComparison (n t s : ℚ) : Prop :=
  let m := 2*n+1
  let cap := (s - max 0 (2*t-n)) / (t-s)
  let top := 1 + m*(n*s-t^2)/(n*(t-s))
  2*top*(top-1)*(top+1)^2 < m*(1-cap^2)

/-- All three post-Johnson endpoint comparisons. -/
theorem production_fourth_comparisons :
    fourthComparison 1073741824 759250112 536870911 ∧
    fourthComparison 1073741824 379625035 134217727 ∧
    fourthComparison 1073741824 268435422 67108863 := by
  norm_num [fourthComparison, max_def]

end ProximityGap.SupportDeficitFourthMoment

#print axioms ProximityGap.SupportDeficitFourthMoment.secondMoment_ge_size
#print axioms ProximityGap.SupportDeficitFourthMoment.spectralFourthUpper
#print axioms ProximityGap.SupportDeficitFourthMoment.entryFourthLower
#print axioms ProximityGap.SupportDeficitFourthMoment.production_fourth_comparisons
