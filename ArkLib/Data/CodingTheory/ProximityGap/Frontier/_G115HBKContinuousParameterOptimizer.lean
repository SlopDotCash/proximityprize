/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# G115: sharp continuous optimizer for the effective HBK parameters

After removing the common powers of `h` and `T`, the HBK Stepanov constraints are

* `a * b ≤ 1` (the monomial-count/nonvanishing constraint), and
* `d * (a + d) ≤ a * b^2` (enough coefficients for multiplicity `d`).

The leading prefix coefficient is `K = 2b/d`.  This file proves algebraically that every
positive feasible triple has `K^3 ≥ 32`, and exhibits equality at
`a = d = 1/c`, `b = c`, `c^3 = 2`.  Thus `K = 2^(5/3)` is the sharp continuous constant;
the remaining effective-HBK work is purely the finite floor/end-point overhead. Issue #466.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer

/-- Eliminating `a` from the two Stepanov feasibility constraints. -/
theorem reduced_feasibility
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a * b ≤ 1) (hmult : d * (a + d) ≤ a * b ^ 2) :
    b * d ^ 2 + d ≤ b ^ 2 := by
  have hbd : 0 ≤ b ^ 2 - d := by
    by_contra h
    have hneg : b ^ 2 - d < 0 := lt_of_not_ge h
    have hprod : a * (b ^ 2 - d) < 0 := mul_neg_of_pos_of_neg ha hneg
    nlinarith [sq_nonneg d]
  have hfirst : d ^ 2 ≤ a * (b ^ 2 - d) := by
    nlinarith
  have hscaled : b * d ^ 2 ≤ (a * b) * (b ^ 2 - d) := by
    nlinarith [mul_nonneg hb.le hbd]
  have hcap : (a * b) * (b ^ 2 - d) ≤ b ^ 2 - d := by
    exact mul_le_of_le_one_left hbd hab
  nlinarith [hscaled.trans hcap]

/-- **Sharp optimizer inequality.** Every positive feasible parameter triple satisfies
`b^3 ≥ 4d^3`, equivalently `(2b/d)^3 ≥ 32`. -/
theorem sharp_cubic_ratio
    {a b d : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hab : a * b ≤ 1) (hmult : d * (a + d) ≤ a * b ^ 2) :
    4 * d ^ 3 ≤ b ^ 3 := by
  have hred := reduced_feasibility ha hb hab hmult
  have hx : 0 ≤ b * d ^ 2 + d := by positivity
  have hsqle : (b * d ^ 2 + d) ^ 2 ≤ (b ^ 2) ^ 2 :=
    (sq_le_sq₀ hx (sq_nonneg b)).2 hred
  have hamgm : 4 * b * d ^ 3 ≤ (b * d ^ 2 + d) ^ 2 := by
    nlinarith [sq_nonneg (b * d ^ 2 - d)]
  have hfour : 4 * b * d ^ 3 ≤ b ^ 4 := by
    calc
      4 * b * d ^ 3 ≤ (b * d ^ 2 + d) ^ 2 := hamgm
      _ ≤ (b ^ 2) ^ 2 := hsqle
      _ = b ^ 4 := by ring
  apply le_of_mul_le_mul_left (a := b) (by
    show b * (4 * d ^ 3) ≤ b * b ^ 3
    nlinarith [hfour]) hb

/-- Ratio form of the sharp lower bound, avoiding real cube roots. -/
theorem normalized_prefix_coefficient_cube_ge
    {a b d K : ℝ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hab : a * b ≤ 1) (hmult : d * (a + d) ≤ a * b ^ 2)
    (hK : K * d = 2 * b) :
    32 ≤ K ^ 3 := by
  have hsharp := sharp_cubic_ratio ha hb hd hab hmult
  have hd3 : 0 < d ^ 3 := pow_pos hd 3
  have hcubes := congrArg (fun x : ℝ => x ^ 3) hK
  have hscaled : 32 * d ^ 3 ≤ 8 * b ^ 3 := by nlinarith
  have heq : K ^ 3 * d ^ 3 = 8 * b ^ 3 := by
    calc
      K ^ 3 * d ^ 3 = (K * d) ^ 3 := by ring
      _ = (2 * b) ^ 3 := hcubes
      _ = 8 * b ^ 3 := by ring
  nlinarith

/-- The cube-root parameter choice attains both feasibility constraints with equality. -/
theorem equality_witness_feasible
    {c : ℝ} (hc : 0 < c) (hc3 : c ^ 3 = 2) :
    (1 / c) * c = 1 ∧
      (1 / c) * ((1 / c) + (1 / c)) = (1 / c) * c ^ 2 := by
  constructor
  · field_simp
  · field_simp
    nlinarith

/-- At the equality witness the normalized prefix coefficient has cube exactly `32`. -/
theorem equality_witness_coefficient_cube
    {c : ℝ} (hc3 : c ^ 3 = 2) :
    (2 * c ^ 2) ^ 3 = 32 := by
  nlinarith [sq_nonneg (c ^ 3 - 2)]

end ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer

#print axioms ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer.reduced_feasibility
#print axioms ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer.sharp_cubic_ratio
#print axioms
  ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer.normalized_prefix_coefficient_cube_ge
#print axioms
  ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer.equality_witness_feasible
#print axioms
  ArkLib.ProximityGap.Frontier.G115HBKContinuousParameterOptimizer.equality_witness_coefficient_cube
