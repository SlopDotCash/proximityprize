/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # Branch-order and ordered-pair genus bounds for the first quarter successor -/

namespace ProximityGap.QuarterSplitBranchOrders
open Finset

/-- Weighted variance with the degree and branch indices inserted. We use actual
fixed-point counts on sheets, so the pair action has F(F-1) fixed points. -/
theorem pair_genus {I : Type*} [Fintype I] (w f : I → ℝ) (m E euler : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hE : 0 < E+2) (weight : ∑ i, w i = E+2)
    (genus0 : ∑ i, w i*f i = m*E+2)
    (pairs : euler = m*(m-1)*E - ∑ i, w i*(f i*(f i-1))) :
    euler * (E+2) ≤ 2*(m-1)^2*E := by
  let s := E+2
  let u := m*E+2
  have variance := sum_nonneg (s := (univ : Finset I))
    (fun i _ => mul_nonneg (hw i) (sq_nonneg (s*f i-u)))
  have expansion (i : I) : w i*(s*f i-u)^2 =
      s^2*(w i*(f i)^2) - 2*s*u*(w i*f i) + u^2*w i := by ring
  simp_rw [expansion] at variance
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    genus0, weight] at variance
  change 0 ≤ s^2*(∑ i, w i*(f i)^2) - 2*s*u*u+u^2*s at variance
  have pos : 0<s := hE
  have lower : u^2 ≤ s*(∑ i, w i*(f i)^2) := by
    apply (mul_le_mul_iff_of_pos_left pos).mp
    nlinarith only [variance]
  have split (i : I) : w i*(f i*(f i-1)) = w i*(f i)^2-w i*f i := by ring
  simp_rw [split] at pairs
  rw [sum_sub_distrib,genus0] at pairs
  dsimp [s,u] at lower
  rw [pairs]
  nlinarith only [lower]

/-- Combine the cubed subgroup count on the pulled-back curves with the
ordered-pair genus bound, retaining the quadratic source degree. -/
theorem torsion_genus {n D h m E euler : ℝ} (hh : 0<h) (hm : 1<m) (hE : 0≤E+2)
    (count : (3*D*h*(m-1))^3 ≤ 54*n^2*h^4*(m-1)^2*(euler+4*(m-1)))
    (pair : euler*(E+2) ≤ 2*(m-1)^2*E) :
    D^3*(E+2) ≤ 2*n^2*(2*(h*m-h)*E+4*h*(E+2)) := by
  have reduced : D^3*(m-1) ≤ 2*n^2*h*(euler+4*(m-1)) := by
    apply (mul_le_mul_iff_of_pos_left (show 0 < 27*h^3*(m-1)^2 by positivity)).mp
    convert count using 1 <;> ring
  have bound := (mul_le_mul_of_nonneg_right reduced hE).trans
    (show 2*n^2*h*(euler+4*(m-1))*(E+2) ≤
        2*n^2*h*(2*(m-1)^2*E+4*(m-1)*(E+2)) by
      rw [mul_assoc,add_mul]
      exact mul_le_mul_of_nonneg_left (add_le_add pair le_rfl) (by positivity))
  apply (mul_le_mul_iff_of_pos_left (sub_pos.mpr hm)).mp
  convert bound using 1 <;> ring

/-- The torsion multiplicity upper bound combined with the normalized pair
genus bound forces this linear inequality in the branch excess. -/
theorem obstruction {n D t h E : ℝ}
    (bound : D^3*(E+2) ≤ 2*n^2*(2*(t-h)*E+4*h*(E+2))) :
    2*(D^3-8*h*n^2) ≤ (4*n^2*(t+h)-D^3)*E := by linarith only [bound]

/-- Numerical branch-excess lower bounds for each first nonquadratic prefix
degree, allowing either admissible quadratic source involution. -/
theorem named {m h E : ℝ} (hpos : 0 ≤ E) (h2 : h ≤ 2)
    (odd : m = 19173961 ∨ m = 134217727 → h ≤ 1)
    (bound : 2*(268435454^3-8*h*1073741824^2) ≤
      (4*1073741824^2*(m+h)-268435454^3)*E) :
    (m = 19173961 → 559999/1000000 < E) ∧ (m = 38347922 → 245613/1000000 < E) ∧
    (m = 134217727 → 64516/1000000 < E) ∧ (m = 268435454 → 31746/1000000 < E) := by
  have test (t a b : ℝ) (ht : m=t) (ha : h ≤ a)
      (cmp : (4*1073741824^2*(t+a)-268435454^3)*b < 2*(268435454^3-8*a*1073741824^2))
      (positive : 0 < 4*1073741824^2*(t+a)-268435454^3) : b < E := by
    apply (mul_lt_mul_iff_of_pos_left positive).mp
    have prod := mul_le_mul_of_nonneg_right ha hpos
    rw [ht] at bound
    nlinarith only [bound,cmp,prod,ha]
  refine ⟨fun ht => test _ 1 _ ht (odd (Or.inl ht)) (by norm_num) (by norm_num),
    fun ht => test _ 2 _ ht h2 (by norm_num) (by norm_num),
    fun ht => test _ 1 _ ht (odd (Or.inr ht)) (by norm_num) (by norm_num),
    fun ht => test _ 2 _ ht h2 (by norm_num) (by norm_num)⟩

#print axioms torsion_genus
#print axioms pair_genus
#print axioms obstruction
#print axioms named
end ProximityGap.QuarterSplitBranchOrders
