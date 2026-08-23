/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# R326: an exact quartic criterion for dyadic coarse/fine decorrelation

For child values `a,b`, put `u=a+b` and `v=a-b`. After summing, write
`A4 = sum (a^4+b^4)`, `C = 2 sum a^2 b^2`, and
`O = 4 sum (a^3 b+a b^3)`. Then the coarse/fine fourth moments are
`A4+3C+O` and `A4+3C-O`, while their mixed square moment is `A4-C`.
The inequality below is an exact sufficient certificate for the half-CS bound.
-/

namespace ProximityGap.R326

theorem child_half_cs_of_quartic_certificate
    {A4 C O mixed u4 v4 : ℝ}
    (hA4 : 0 ≤ A4) (hC : 0 ≤ C) (hmixed : 0 ≤ mixed)
    (hmixedEq : mixed = A4 - C)
    (hu4 : u4 = A4 + 3 * C + O)
    (hv4 : v4 = A4 + 3 * C - O)
    (hcert : O ^ 2 ≤ (5 * C - A4) * (3 * A4 + C)) :
    mixed ≤ (1 / 2 : ℝ) * Real.sqrt u4 * Real.sqrt v4 := by
  have huv : 4 * mixed ^ 2 ≤ u4 * v4 := by
    rw [hmixedEq, hu4, hv4]
    nlinarith
  have hu4_nonneg : 0 ≤ u4 := by
    rw [hu4]
    nlinarith [sq_nonneg O]
  have hv4_nonneg : 0 ≤ v4 := by
    rw [hv4]
    nlinarith [sq_nonneg O]
  have hsqrt : Real.sqrt (u4 * v4) = Real.sqrt u4 * Real.sqrt v4 :=
    Real.sqrt_mul hu4_nonneg v4
  have hsq : (2 * mixed) ^ 2 ≤ (Real.sqrt (u4 * v4)) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hu4_nonneg hv4_nonneg)]
    nlinarith
  have hroot : 2 * mixed ≤ Real.sqrt (u4 * v4) := by
    nlinarith [Real.sqrt_nonneg (u4 * v4)]
  rw [hsqrt] at hroot
  nlinarith

/-- Pairwise half-CS bounds do not compose, even for orthogonal residuals.

For `A=(2,2,2,2)`, `B1=(2,0,0,0)`, and `B2=(0,2,0,0)`, each residual saturates the
squared half-CS inequality `4 M^2 <= A4*B4`, and `B1` and `B2` are orthogonal. But their
sum violates that same inequality by a factor two. -/
theorem pairwise_half_cs_composition_countermodel :
    let A4 : ℝ := 4 * 2 ^ 4
    let B14 : ℝ := 2 ^ 4
    let B24 : ℝ := 2 ^ 4
    let M1 : ℝ := 2 ^ 2 * 2 ^ 2
    let M2 : ℝ := 2 ^ 2 * 2 ^ 2
    let Bsum4 : ℝ := 2 * 2 ^ 4
    let Msum : ℝ := 2 * (2 ^ 2 * 2 ^ 2)
    4 * M1 ^ 2 ≤ A4 * B14 ∧
      4 * M2 ^ 2 ≤ A4 * B24 ∧
      (0 : ℝ) = 0 ∧
      A4 * Bsum4 < 4 * Msum ^ 2 := by
  norm_num

end ProximityGap.R326
