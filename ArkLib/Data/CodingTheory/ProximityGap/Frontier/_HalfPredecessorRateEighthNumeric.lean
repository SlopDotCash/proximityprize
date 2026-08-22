/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The weighted third-moment numeric core at rate at most `1/8`

Let `n = 2h`, let the agreement threshold be `h+1`, and put
`d = h/4-1`.  The rich-line stratification in
`docs/kb/deltastar-466-half-predecessor-rate-eighth-2026-07-09.md` gives

* the usual noncollinear contribution `d * N(N-1)(N-2)`;
* a contribution at most `(3h/2-6) * N(N-1)` from lines containing at
  most four selected points;
* at most fifteen exceptional lines, each containing at most one hundred
  points, hence an additional contribution at most
  `90 * choose(100,3) * (3h/4-3)`.

All displayed quantities are six times the third incidence moment.  This
file proves that the balanced Jensen lower bound strictly exceeds their sum
for `h >= 2048` and `N >= 2h+1`.  The constant `2048` is deliberately round;
the exact endpoint changes sign between `h=1472` and `h=1476`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric

/-- Six times the balanced/Jensen lower bound for the third incidence moment. -/
def lowerSix (h N : ℕ) : ℚ :=
  let a : ℚ := (N : ℚ) * ((h : ℚ) + 1) / (2 * (h : ℚ))
  2 * (h : ℚ) * a * (a - 1) * (a - 2)

/-- Six times the contribution from noncollinear triples and from all lines
of size at most four. -/
def bulkUpperSix (h N : ℕ) : ℚ :=
  ((h : ℚ) / 4 - 1) * (N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) +
    (3 * (h : ℚ) / 2 - 6) * (N : ℚ) * ((N : ℚ) - 1)

/-- Six times the coarse correction for at most fifteen exceptional lines,
each of size at most one hundred.  Here `choose(100,3)=161700`. -/
def exceptionalUpperSix (h : ℕ) : ℚ :=
  90 * 161700 * (3 * (h : ℚ) / 4 - 3)

/-- The quadratic remaining after removing the factor `N` from the balanced
lower bound minus the bulk upper bound. -/
def gapQuadratic (h N : ℕ) : ℚ :=
  (7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2)) * (N : ℚ)^2 -
    (9 * (h : ℚ) / 4 + 3 / (2 * (h : ℚ))) * (N : ℚ) +
    3 * (h : ℚ) - 2

/-- Exact factorization of the bulk gap. -/
theorem lowerSix_sub_bulkUpperSix_eq (h N : ℕ) (hh : 0 < h) :
    lowerSix h N - bulkUpperSix h N = (N : ℚ) * gapQuadratic h N := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [lowerSix, bulkUpperSix, gapQuadratic]
  push_cast
  field_simp [hhq]
  ring

/-- The endpoint quadratic is manifestly positive after clearing `4h²`. -/
theorem gapQuadratic_endpoint (h : ℕ) (hh : 0 < h) :
    4 * (h : ℚ)^2 * gapQuadratic h (2 * h + 1) =
      10 * (h : ℚ)^4 + 43 * (h : ℚ)^3 + 3 * (h : ℚ)^2 +
        (h : ℚ) + 1 := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [gapQuadratic]
  push_cast
  field_simp [hhq]
  ring

/-- The gap quadratic is increasing throughout the counterexample range. -/
theorem gapQuadratic_mono_from_endpoint (h N : ℕ) (hh : 1 ≤ h)
    (hN : 2 * h + 1 ≤ N) :
    gapQuadratic h (2 * h + 1) ≤ gapQuadratic h N := by
  have hhpos : 0 < h := by omega
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hhpos
  have hNq : (2 * (h : ℚ) + 1) ≤ (N : ℚ) := by exact_mod_cast hN
  let A : ℚ := 7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2)
  let B : ℚ := 9 * (h : ℚ) / 4 + 3 / (2 * (h : ℚ))
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hslope : B < 2 * A * (2 * (h : ℚ) + 1) := by
    dsimp only [A, B]
    have hh1 : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    field_simp
    nlinarith [sq_nonneg ((h : ℚ) - 1), mul_pos hhq hhq]
  have hbracket : 0 ≤ A * ((N : ℚ) + (2 * (h : ℚ) + 1)) - B := by
    have hsum : 2 * (2 * (h : ℚ) + 1) ≤
        (N : ℚ) + (2 * (h : ℚ) + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsum hA.le
    nlinarith
  have hfactor :
      gapQuadratic h N - gapQuadratic h (2 * h + 1) =
        ((N : ℚ) - (2 * (h : ℚ) + 1)) *
          (A * ((N : ℚ) + (2 * (h : ℚ) + 1)) - B) := by
    simp only [gapQuadratic, A, B]
    push_cast
    ring
  apply sub_nonneg.mp
  rw [hfactor]
  exact mul_nonneg (sub_nonneg.mpr hNq) hbracket

/-- After pruning the union of the exceptional (`L ≥ 5`) lines, the
remaining family has size `N > 9h/7`.  This is already strictly beyond the
positive root of the rate-`1/8` bulk gap. -/
theorem gapQuadratic_pos_of_nine_mul_lt_seven_mul (h N : ℕ) (hh : 1 ≤ h)
    (hN : 9 * h < 7 * N) :
    0 < gapQuadratic h N := by
  have hhpos : 0 < h := by omega
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hhpos
  have hhq1 : (1 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
  have hNmul : 9 * (h : ℚ) < 7 * (N : ℚ) := by exact_mod_cast hN
  let A : ℚ := 7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2)
  let B : ℚ := 9 * (h : ℚ) / 4 + 3 / (2 * (h : ℚ))
  let x₀ : ℚ := 9 * (h : ℚ) / 7
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hxN : x₀ < (N : ℚ) := by
    dsimp only [x₀]
    apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 7)).2
    linarith
  have hslope : B < 2 * A * x₀ := by
    dsimp only [A, B, x₀]
    field_simp
    nlinarith [sq_nonneg ((h : ℚ) - 1), mul_pos hhq hhq]
  have hbracket : 0 < A * ((N : ℚ) + x₀) - B := by
    have hsum : 2 * x₀ < (N : ℚ) + x₀ := by linarith
    have hmul := mul_lt_mul_of_pos_left hsum hA
    nlinarith
  have hbaseEq :
      A * x₀^2 - B * x₀ + 3 * (h : ℚ) - 2 =
        (831 * (h : ℚ) - 689) / 196 := by
    dsimp only [A, B, x₀]
    field_simp
    ring
  have hbase : 0 < A * x₀^2 - B * x₀ + 3 * (h : ℚ) - 2 := by
    rw [hbaseEq]
    have hnum : (0 : ℚ) < 831 * (h : ℚ) - 689 := by linarith
    exact div_pos hnum (by norm_num)
  have hfactor :
      gapQuadratic h N -
          (A * x₀^2 - B * x₀ + 3 * (h : ℚ) - 2) =
        ((N : ℚ) - x₀) * (A * ((N : ℚ) + x₀) - B) := by
    simp only [gapQuadratic, A, B]
    ring
  have hdiff : 0 <
      gapQuadratic h N -
        (A * x₀^2 - B * x₀ + 3 * (h : ℚ) - 2) := by
    rw [hfactor]
    exact mul_pos (sub_pos.mpr hxN) hbracket
  linarith

/-- The pruned-family numeric contradiction: once every remaining line has
size at most four, `9h < 7N` alone makes the bulk upper bound strictly smaller
than the Jensen lower bound. -/
theorem bulkUpperSix_lt_lowerSix_of_nine_mul_lt_seven_mul
    (h N : ℕ) (hh : 1 ≤ h) (hN : 9 * h < 7 * N) :
    bulkUpperSix h N < lowerSix h N := by
  have hhpos : 0 < h := by omega
  have hNpos : 0 < N := by omega
  have hgap := gapQuadratic_pos_of_nine_mul_lt_seven_mul h N hh hN
  have hid := lowerSix_sub_bulkUpperSix_eq h N hhpos
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  nlinarith [mul_pos hNq hgap]

/-- Abstract contradiction consumer for the simpler exceptional-line pruning
route. -/
theorem nine_mul_le_seven_mul_of_bulk_thirdMoment_bounds
    (h N : ℕ) (T : ℚ) (hh : 1 ≤ h)
    (hlower : lowerSix h N ≤ 6 * T)
    (hupper : 6 * T ≤ bulkUpperSix h N) :
    7 * N ≤ 9 * h := by
  by_contra hnot
  have hN : 9 * h < 7 * N := by omega
  have hgap := bulkUpperSix_lt_lowerSix_of_nine_mul_lt_seven_mul h N hh hN
  linarith

/-- Exact positive expansion of the full endpoint margin about `h=2048`.
Every coefficient in the shifted variable is positive. -/
theorem endpoint_margin_expansion (h : ℕ) (hh : 0 < h) :
    4 * (h : ℚ)^2 *
        (((2 * h + 1 : ℕ) : ℚ) * gapQuadratic h (2 * h + 1) -
          exceptionalUpperSix h) =
      347969733288531969 +
        1213875709956099 * ((h : ℚ) - 2048) +
        1452336878565 * ((h : ℚ) - 2048)^2 +
        795988281 * ((h : ℚ) - 2048)^3 +
        204896 * ((h : ℚ) - 2048)^4 +
        20 * ((h : ℚ) - 2048)^5 := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [gapQuadratic, exceptionalUpperSix]
  push_cast
  field_simp [hhq]
  ring

/-- The full endpoint margin is positive for the round production-safe cutoff
`h >= 2048`. -/
theorem exceptionalUpperSix_lt_endpoint_gap (h : ℕ) (hh : 2048 ≤ h) :
    exceptionalUpperSix h <
      ((2 * h + 1 : ℕ) : ℚ) * gapQuadratic h (2 * h + 1) := by
  have hhpos : 0 < h := by omega
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hhpos
  have hhq2048 : (2048 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
  have hx : (0 : ℚ) ≤ (h : ℚ) - 2048 := sub_nonneg.mpr hhq2048
  have hexp := endpoint_margin_expansion h hhpos
  have hscale : (0 : ℚ) < 4 * (h : ℚ)^2 := by positivity
  have hrhs : (0 : ℚ) <
      347969733288531969 +
        1213875709956099 * ((h : ℚ) - 2048) +
        1452336878565 * ((h : ℚ) - 2048)^2 +
        795988281 * ((h : ℚ) - 2048)^3 +
        204896 * ((h : ℚ) - 2048)^4 +
        20 * ((h : ℚ) - 2048)^5 := by
    positivity
  nlinarith

/-- **Strict weighted third-moment gap at rate `1/8`.** -/
theorem bulk_add_exceptional_lt_lowerSix (h N : ℕ)
    (hh : 2048 ≤ h) (hN : 2 * h + 1 ≤ N) :
    bulkUpperSix h N + exceptionalUpperSix h < lowerSix h N := by
  have hhpos : 0 < h := by omega
  have hNpos : 0 < N := by omega
  have hmono := gapQuadratic_mono_from_endpoint h N (by omega) hN
  have hq0scaled := gapQuadratic_endpoint h hhpos
  have hq0 : 0 < gapQuadratic h (2 * h + 1) := by
    have hscale : (0 : ℚ) < 4 * (h : ℚ)^2 := by positivity
    have hpoly : (0 : ℚ) <
        10 * (h : ℚ)^4 + 43 * (h : ℚ)^3 + 3 * (h : ℚ)^2 +
          (h : ℚ) + 1 := by positivity
    nlinarith
  have hqN : 0 < gapQuadratic h N := lt_of_lt_of_le hq0 hmono
  have hNq : (((2 * h + 1 : ℕ) : ℚ)) ≤ (N : ℚ) := by exact_mod_cast hN
  have hprod :
      (((2 * h + 1 : ℕ) : ℚ)) * gapQuadratic h (2 * h + 1) ≤
        (N : ℚ) * gapQuadratic h N := by
    exact mul_le_mul hNq hmono hq0.le (by positivity)
  have hend := exceptionalUpperSix_lt_endpoint_gap h hh
  have hid := lowerSix_sub_bulkUpperSix_eq h N hhpos
  nlinarith

/-- Abstract contradiction consumer for the geometric incidence theorem. -/
theorem card_le_two_mul_of_weighted_thirdMoment_bounds
    (h N : ℕ) (T : ℚ) (hh : 2048 ≤ h)
    (hlower : lowerSix h N ≤ 6 * T)
    (hupper : 6 * T ≤ bulkUpperSix h N + exceptionalUpperSix h) :
    N ≤ 2 * h := by
  by_contra hnot
  have hN : 2 * h + 1 ≤ N := by omega
  have hgap := bulk_add_exceptional_lt_lowerSix h N hh hN
  linarith

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric

#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.lowerSix_sub_bulkUpperSix_eq
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.gapQuadratic_mono_from_endpoint
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.gapQuadratic_pos_of_nine_mul_lt_seven_mul
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.bulkUpperSix_lt_lowerSix_of_nine_mul_lt_seven_mul
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.endpoint_margin_expansion
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.bulk_add_exceptional_lt_lowerSix
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthNumeric.card_le_two_mul_of_weighted_thirdMoment_bounds
