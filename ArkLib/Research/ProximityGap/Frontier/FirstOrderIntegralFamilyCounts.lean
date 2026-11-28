/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.RoundedCounts
import Mathlib.Tactic

/-! # Degree and slot comparisons for integral families of polynomial solutions -/

namespace ProximityGap.FirstOrderIntegralFamilyCounts
open Finset ReedSolomon.HiddenDerivative

/-- Affine intersection bound after removing the forced intersection at infinity. -/
def affineBound (b v D w : ℤ) : ℤ := v * D + (b - v) * w

/-- Combined intersection price for the derivative numerator and the separant. -/
def isolatedBound (b v d : ℤ) : ℤ :=
  2 * b * v - v ^ 2 + d * (4 * b * v - b - 2 * v ^ 2 - v)

/-- Accounting for the two derivative degrees in the projective Bézout bound. -/
theorem derivative_degree_charge (b v d : ℤ) :
    affineBound b v (1 + 2 * d * (b - 1)) (1 + d * (2 * v - 1)) +
      affineBound b v (b - 1) (v - 1) = isolatedBound b v d := by
  unfold affineBound isolatedBound
  ring

/-- Irreducible factors can share the total and first-derivative degree budgets. -/
theorem sum_factor_charge {b v c w d : ℤ} (hb : v ≤ b) (hc : w ≤ c)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hd : 0 ≤ d) :
    isolatedBound b v d + isolatedBound c w d ≤ isolatedBound (b + c) (v + w) d := by
  have extra : 0 ≤ (b - v) * w + v * c := by
    have : 0 ≤ c := le_trans hw hc
    positivity
  have scale : 0 ≤ 2 + 4 * d := by positivity
  unfold isolatedBound
  nlinarith only [mul_nonneg scale extra]

/-- Unknown scalar coefficients of a first-order differential polynomial in the truncated board. -/
def slots (r t d b v : ℕ) : ℕ :=
  ∑ h ∈ range (v + 1), ∑ j ∈ range (b + 1 - h), (r * t - d * j - (d - 1) * h)

/-- The strict source-rank surplus and the integral-family count after clearing the
positive agreement denominator in the four closed-ball tests. -/
def certificate (q e r b v budget : ℕ) (normalized : Bool := false) : Prop :=
  let n := 2 ^ 30
  let d := n / q - 1
  let t := n - e
  let charge : ℤ := if normalized then
    2 * (b : ℤ) * v - (v : ℤ) ^ 2 + d * (4 * (b : ℤ) * v - 2 * b - 2 * (v : ℤ) ^ 2)
    else isolatedBound b v d
  let families : ℕ := if normalized then v else b * v
  n * firstOrderRankCount r v < slots r t d b v ∧ d < t ∧
    (charge + b) * ((t : ℤ) - d) + (families : ℤ) * ((n : ℤ) - d) ≤
      (budget * n : ℕ) * ((t : ℤ) - d)

instance (q e r b v budget : ℕ) (normalized : Bool) :
    Decidable (certificate q e r b v budget normalized) := by
  unfold certificate
  infer_instance

/-- The four comparison boards at the low-budget first-order radii. -/
theorem production_comparisons :
    certificate 2 318504960 13 18 3 89 ∧ certificate 4 547618816 12 23 3 59 ∧
      certificate 8 706478080 10 27 3 35 ∧ certificate 16 816840704 7 25 4 22 := by
  decide +kernel

/-- The normalized pole count on the eight explicit prime-field instances. -/
theorem normalized_production_comparisons :
    certificate 2 318582739 13 18 3 81 true ∧ certificate 4 547807172 12 23 3 53 true ∧
    certificate 8 706542381 10 27 3 32 true ∧ certificate 16 816890638 7 25 4 20 true ∧
    certificate 2 319220543 14 19 3 89 true ∧ certificate 4 548801377 10 19 4 59 true ∧
    certificate 8 708016270 9 22 4 35 true ∧ certificate 16 818211920 8 27 4 22 true := by
  decide +kernel

#print axioms normalized_production_comparisons
#print axioms derivative_degree_charge
#print axioms sum_factor_charge
#print axioms production_comparisons
end ProximityGap.FirstOrderIntegralFamilyCounts
