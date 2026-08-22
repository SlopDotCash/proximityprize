/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# AJT13: absorbing the principal-character translation

Complete character orthogonality centers a Gauss period `eta` as `eta + 1 / m`, where `m` is
the quotient size.  This file proves that a Wick-coefficient bound for the centered fourteenth
moment implies the public coefficient-`2^18` bound for the uncentered moment as soon as `m >= 21`.

The proof uses the weighted convexity inequality

`(x - c)^14 <= (21/20)^13 x^14 + 21^13 c^14`.

For `m` quotient classes, the total translation error is at most `21^13 / m^13 <= 1`; the
remaining coefficient calculation is

`135135 * (21/20)^13 + 1 < 2^18`.

Thus the principal-character boundary is not a separate production obstruction if the centered
AJT13 moment is controlled at the Wick constant.  Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped BigOperators

namespace ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge

/-- Weighted convexity with weights `20/21` and `1/21`.  The exponent `13` on the two
coefficients is the one-power gain over the usual symmetric `2^13` estimate. -/
theorem sub_shift_pow_fourteen_le (x c : ℝ) :
    (x - c) ^ 14 ≤ ((21 : ℝ) / 20) ^ 13 * x ^ 14 + 21 ^ 13 * c ^ 14 := by
  let w : Bool → ℝ := fun b => if b then 1 / 21 else 20 / 21
  let z : Bool → ℝ := fun b => if b then -(21 * c) else (21 / 20) * x
  have hw : ∀ b ∈ (Finset.univ : Finset Bool), 0 ≤ w b := by
    intro b _
    cases b <;> norm_num [w]
  have hwsum : ∑ b ∈ (Finset.univ : Finset Bool), w b = 1 := by
    norm_num [w]
  have hconv := Real.pow_arith_mean_le_arith_mean_pow_of_even
    (s := (Finset.univ : Finset Bool)) w z hw hwsum (by norm_num : Even 14)
  norm_num [w, z] at hconv ⊢
  convert hconv using 1 <;> ring

/-- With `m >= 21`, the aggregate fourteenth-power cost of translating every one of `m`
coordinates by `1/m` is at most one. -/
theorem translation_boundary_le_one {m : ℝ} (hm : 21 ≤ m) :
    m * 21 ^ 13 * (1 / m) ^ 14 ≤ 1 := by
  have hm0 : m ≠ 0 := by positivity
  calc
    m * 21 ^ 13 * (1 / m) ^ 14 = (21 / m) ^ 13 := by
      field_simp
    _ ≤ 1 ^ 13 := by
      gcongr
      exact (div_le_one (by positivity : 0 < m)).2 hm
    _ = 1 := by norm_num

/-- The Wick coefficient fits inside the public coefficient after the weighted translation. -/
theorem weighted_wick_plus_boundary_lt_public :
    ((21 : ℝ) / 20) ^ 13 * 135135 + 1 < 2 ^ 18 := by
  norm_num

/-- **Centered-to-uncentered AJT13 bridge.**  A centered fourteenth moment at Wick coefficient
`13!! = 135135` implies the public uncentered coefficient `2^18`.  The scalar `Q` is the target
scale (in production, `Q = q*n^6`); only `Q >= 1` and at least 21 quotient classes are needed. -/
theorem uncentered_le_public_of_centered_le_wick
    {I : Type*} [Fintype I] (eta : I → ℝ) (Q : ℝ)
    (hcard : (21 : ℝ) ≤ Fintype.card I) (hQ : 1 ≤ Q)
    (hcenter :
      ∑ i : I, (eta i + 1 / (Fintype.card I : ℝ)) ^ 14 ≤ 135135 * Q) :
    ∑ i : I, eta i ^ 14 ≤ 2 ^ 18 * Q := by
  let m : ℝ := Fintype.card I
  let A : ℝ := ((21 : ℝ) / 20) ^ 13
  have hpoint (i : I) :
      eta i ^ 14 ≤ A * (eta i + 1 / m) ^ 14 + 21 ^ 13 * (1 / m) ^ 14 := by
    have h := sub_shift_pow_fourteen_le (eta i + 1 / m) (1 / m)
    simpa [A] using h
  have hsum :
      ∑ i : I, eta i ^ 14 ≤
        A * (∑ i : I, (eta i + 1 / m) ^ 14) + m * 21 ^ 13 * (1 / m) ^ 14 := by
    calc
      ∑ i : I, eta i ^ 14 ≤
          ∑ i : I, (A * (eta i + 1 / m) ^ 14 + 21 ^ 13 * (1 / m) ^ 14) :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = A * (∑ i : I, (eta i + 1 / m) ^ 14) +
          m * 21 ^ 13 * (1 / m) ^ 14 := by
        rw [Finset.sum_add_distrib]
        congr 1
        · simpa using
            (Finset.mul_sum (Finset.univ : Finset I)
              (fun i => (eta i + 1 / m) ^ 14) A).symm
        · simp [m]
          ring
  have hA : 0 ≤ A := by positivity
  have hcenter' : ∑ i : I, (eta i + 1 / m) ^ 14 ≤ 135135 * Q := by
    simpa [m] using hcenter
  have htranslated : m * 21 ^ 13 * (1 / m) ^ 14 ≤ 1 := by
    exact translation_boundary_le_one (by simpa [m] using hcard)
  have hcoeff : A * 135135 + 1 ≤ (2 : ℝ) ^ 18 := by
    exact (weighted_wick_plus_boundary_lt_public).le
  calc
    ∑ i : I, eta i ^ 14
        ≤ A * (∑ i : I, (eta i + 1 / m) ^ 14) +
            m * 21 ^ 13 * (1 / m) ^ 14 := hsum
    _ ≤ A * (135135 * Q) + 1 := by gcongr
    _ ≤ (A * 135135 + 1) * Q := by
      nlinarith
    _ ≤ 2 ^ 18 * Q := by
      gcongr

end ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge.sub_shift_pow_fourteen_le
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge.translation_boundary_le_one
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge.weighted_wick_plus_boundary_lt_public
#print axioms
  ArkLib.ProximityGap.Frontier.AJT13CenteredBoundaryBridge.uncentered_le_public_of_centered_le_wick
