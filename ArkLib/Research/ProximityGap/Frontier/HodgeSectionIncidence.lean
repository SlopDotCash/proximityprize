/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # Population bounds from surface intersection inequalities

The inputs below are the numerical intersection inequalities on an interpolation
surface. The construction of that surface, ramification estimate and geometric
incidence interpretation are the hypotheses of the accompanying written argument.
-/

namespace ProximityGap.HodgeSectionIncidence

open Finset

/-- The negative-semidefinite intersection inequality and a bound on the sum of
the received curves' self-intersection defects give a linear cost per incidence. -/
theorem bessel_cost {scale j a c x h : ℝ} (hscale : 0 ≤ scale) (hj : 0 ≤ j)
    (hc : 0 ≤ c) (hh : 0 ≤ h) (hinc : scale*j ≤ x) (hindex : x^2 ≤ a*c)
    (hdefect : a ≤ h*j) : scale^2*j ≤ h*c := by
  by_cases hz : j = 0
  · simpa [hz] using mul_nonneg hh hc
  apply (mul_le_mul_iff_of_pos_right (lt_of_le_of_ne hj (Ne.symm hz))).mp
  calc
    scale^2*j*j = (scale*j)^2 := by ring
    _ ≤ x^2 := (sq_le_sq₀ (mul_nonneg hscale hj) ((mul_nonneg hscale hj).trans hinc)).mpr hinc
    _ ≤ a*c := hindex
    _ ≤ (h*j)*c := mul_le_mul_of_nonneg_right hdefect hc
    _ = h*c*j := by ring

/-- Summing local section costs under the ramification bound gives the relaxed
incidence estimate in Theorem A, with the two affine branch-degree corrections. -/
theorem total_incidences {ι : Type*} (S : Finset ι) (j c : ι → ℝ)
    {b h g a β₁ β₂ : ℝ} (hb : 2 ≤ b) (hh : 1 ≤ h) (hg : 0 ≤ g)
    (ha : 0 ≤ a) (hβ : 0 ≤ β₁) (hβ' : 0 ≤ β₂)
    (hX : β₁ ≤ (2*b-2)*g+1) (hΓ : β₂ ≤ (2*b-2)*a+1)
    (hbudget : ∑ i ∈ S, c i ≤ 4*β₁*β₂)
    (hlocal : ∀ i ∈ S, ((b-1)/b)^2*j i ≤ (h-1)*c i) :
    ∑ i ∈ S, j i ≤ 16*b^2*(a+1)*(g+1)*(h-1) := by
  have hb' : 0 < b := by linarith
  have hlinear : 0 < b-1 := by linarith
  have hscale : 0 < ((b-1)/b)^2 := by positivity
  apply (mul_le_mul_iff_of_pos_left hscale).mp
  have hsum := sum_le_sum hlocal
  rw [← mul_sum, ← mul_sum] at hsum
  have hd1 : β₁ ≤ (2*(b-1))*(g+1) := by linarith
  have hd2 : β₂ ≤ (2*(b-1))*(a+1) := by linarith
  have hprod := mul_le_mul hd1 hd2 hβ' (hβ.trans hd1)
  calc
    _ ≤ (h-1)*∑ i ∈ S, c i := hsum
    _ ≤ (h-1)*(4*β₁*β₂) := mul_le_mul_of_nonneg_left hbudget (by linarith)
    _ ≤ (h-1)*(4*((2*(b-1))*(g+1))*((2*(b-1))*(a+1))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    _ = _ := by field_simp; ring

/-- Integral form of the displayed bound, rounding only after the incidence
allowance and the exceptional-site allowance have been added. -/
def populationBound (n t d b g h a W : ℕ) : ℕ :=
  (4*b-2)*g+1 + (16*b^2*(a+1)*(g+1)*(h-1)+h*n)/(t+d-W)

/-- If the incidence, exceptional-scalar and agreement counts satisfy Corollary B's
geometric bounds, the full population satisfies its stated integer bound. -/
theorem population_of_counts {n t d b g h a W N G J : ℕ}
    (hpositive : W < t+d) (hremoved : N ≤ G+((4*b-2)*g+1))
    (hfit : G*(t+d-W) ≤ J+h*n) (hJ : J ≤ 16*b^2*(a+1)*(g+1)*(h-1)) :
    N ≤ populationBound n t d b g h a W := by
  have hG : G ≤ (16*b^2*(a+1)*(g+1)*(h-1)+h*n)/(t+d-W) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    omega
  unfold populationBound
  omega

/-- Corollary B from the geometric section costs, branch degrees and agreement
counts. The site and exceptional-scalar counts remain separate assumptions. -/
theorem population_of_intersections {ι : Type*} (S : Finset ι) (j : ι → ℕ) (c : ι → ℝ)
    {n t d b g h a W N : ℕ} {β₁ β₂ : ℝ} (hb : 2 ≤ b) (hh : 1 ≤ h)
    (hβ : 0 ≤ β₁) (hβ' : 0 ≤ β₂)
    (hX : β₁ ≤ (2*(b:ℝ)-2)*g+1) (hΓ : β₂ ≤ (2*(b:ℝ)-2)*a+1)
    (hbudget : ∑ i ∈ S, c i ≤ 4*β₁*β₂)
    (hlocal : ∀ i ∈ S, (((b:ℝ)-1)/b)^2*(j i : ℝ) ≤ ((h:ℝ)-1)*c i)
    (hpositive : W < t+d) (hremoved : N ≤ S.card+((4*b-2)*g+1))
    (hfit : S.card*(t+d-W) ≤ (∑ i ∈ S, j i)+h*n) :
    N ≤ populationBound n t d b g h a W := by
  apply population_of_counts hpositive hremoved hfit
  have bound := total_incidences S (fun i => (j i : ℝ)) c
    (by exact_mod_cast hb) (by exact_mod_cast hh)
    (Nat.cast_nonneg g) (Nat.cast_nonneg a) hβ hβ' hX hΓ hbudget hlocal
  rw [← Nat.cast_one, ← Nat.cast_sub hh] at bound
  exact_mod_cast bound

/-- Relaxing both the coordinate degree and weight to the interpolation budget
gives the general terminal values. The sharper rows use the measured weights of
the actual cubic and quartic alternatives. -/
theorem terminal_bounds :
    populationBound 1073741824 357913943 67108863 3 34 34 357913942 357913942 = 887925 ∧
    populationBound 1073741824 357913943 67108863 4 34 34 357913942 357913942 = 1577981 ∧
    populationBound 1073741824 357913943 67108863 3 34 34 290805098 290805098 = 360973 ∧
    populationBound 1073741824 357913943 67108863 4 34 34 302954072 302954072 = 734604 := by
  decide

#print axioms bessel_cost
#print axioms total_incidences
#print axioms population_of_counts
#print axioms population_of_intersections
#print axioms terminal_bounds

end ProximityGap.HodgeSectionIncidence
