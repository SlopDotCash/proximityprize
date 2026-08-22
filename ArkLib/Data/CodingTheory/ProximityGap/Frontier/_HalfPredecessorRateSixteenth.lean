/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The numeric third-moment core of the rate-`1/16` half-predecessor theorem

The accompanying paper proof is
`docs/kb/deltastar-466-half-predecessor-rate-sixteenth-2026-07-09.md`.

For a length `n = 2h` RS code at agreement `t = h+1`, the lifted rich-point argument
reduces a hypothetical set of `N > 2h` bad scalars to two bounds on six times its
third incidence moment.  At dimension `k ≤ n/16`, hence `d = k-1 ≤ h/8-1`, they are

```text
lower = 2h * a(a-1)(a-2),       a = N(h+1)/(2h),
upper = (h/8-1)N(N-1)(N-2) + 2(5h/8-5/2)N(N-1).
```

This file machine-checks the strict numeric separation and packages the contradiction
consumer.  The geometric inputs (line-core dichotomy, line size at most four,
noncollinear triple codegree at most `d`) remain explicit hypotheses of the consumer;
there is no hidden higher-order-MDS assumption.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth

/-- Six times the balanced/Jensen lower bound for the third incidence moment. -/
def lowerSix (h N : ℕ) : ℚ :=
  let a : ℚ := (N : ℚ) * ((h : ℚ) + 1) / (2 * (h : ℚ))
  2 * (h : ℚ) * a * (a - 1) * (a - 2)

/-- Six times the worst-case third-moment upper bound after the line-core dichotomy. -/
def upperSix (h N : ℕ) : ℚ :=
  ((h : ℚ) / 8 - 1) * (N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) +
    2 * (5 * (h : ℚ) / 8 - 5 / 2) * (N : ℚ) * ((N : ℚ) - 1)

/-- The quadratic obtained after subtracting `upperSix` from `lowerSix` and
dividing by the positive factor `N`. -/
def gapQuadratic (h N : ℕ) : ℚ :=
  ((h : ℚ) / 8 + 7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2)) * (N : ℚ)^2 -
    (19 * (h : ℚ) / 8 + 1 + 3 / (2 * (h : ℚ))) * (N : ℚ) +
    3 * (h : ℚ) - 1

/-- Exact algebraic identity behind the numeric comparison. -/
theorem lowerSix_sub_upperSix_eq (h N : ℕ) (hh : 0 < h) :
    lowerSix h N - upperSix h N = (N : ℚ) * gapQuadratic h N := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [lowerSix, upperSix, gapQuadratic]
  push_cast
  field_simp [hhq]
  ring

/-- The endpoint value of the quadratic has a manifestly positive numerator. -/
theorem gapQuadratic_endpoint (h : ℕ) (hh : 0 < h) :
    8 * (h : ℚ)^2 * gapQuadratic h (2 * h + 1) =
      4 * (h : ℚ)^5 + 22 * (h : ℚ)^4 + 70 * (h : ℚ)^3 +
        6 * (h : ℚ)^2 + 2 * (h : ℚ) + 2 := by
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  simp only [gapQuadratic]
  push_cast
  field_simp [hhq]
  ring

/-- The quadratic is strictly increasing on the whole counterexample range
`N ≥ 2h+1`, for `h ≥ 8`. -/
theorem gapQuadratic_mono_from_endpoint (h N : ℕ) (hh : 8 ≤ h)
    (hN : 2 * h + 1 ≤ N) :
    gapQuadratic h (2 * h + 1) ≤ gapQuadratic h N := by
  have hhpos : 0 < h := by omega
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hhpos
  have hNq : (2 * (h : ℚ) + 1) ≤ (N : ℚ) := by exact_mod_cast hN
  have hcoef :
      0 < (h : ℚ) / 8 + 7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2) := by
    positivity
  have hslope :
      19 * (h : ℚ) / 8 + 1 + 3 / (2 * (h : ℚ)) <
        2 * ((h : ℚ) / 8 + 7 / 4 + 3 / (4 * (h : ℚ)) +
          1 / (4 * (h : ℚ)^2)) * (2 * (h : ℚ) + 1) := by
    have hh8 : (8 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
    field_simp
    nlinarith [sq_nonneg ((h : ℚ) - 8), mul_pos hhq hhq]
  let A : ℚ :=
    (h : ℚ) / 8 + 7 / 4 + 3 / (4 * (h : ℚ)) + 1 / (4 * (h : ℚ)^2)
  let B : ℚ := 19 * (h : ℚ) / 8 + 1 + 3 / (2 * (h : ℚ))
  have hbracket : 0 ≤ A * ((N : ℚ) + (2 * (h : ℚ) + 1)) - B := by
    dsimp only [A, B]
    have hsum : 2 * (2 * (h : ℚ) + 1) ≤ (N : ℚ) + (2 * (h : ℚ) + 1) := by
      linarith
    have := mul_le_mul_of_nonneg_left hsum hcoef.le
    nlinarith
  have hfactor :
      gapQuadratic h N - gapQuadratic h (2 * h + 1) =
        ((N : ℚ) - (2 * (h : ℚ) + 1)) *
          (A * ((N : ℚ) + (2 * (h : ℚ) + 1)) - B) := by
    simp only [gapQuadratic, A, B]
    push_cast
    ring
  have hfirst : 0 ≤ (N : ℚ) - (2 * (h : ℚ) + 1) := sub_nonneg.mpr hNq
  apply sub_nonneg.mp
  rw [hfactor]
  exact mul_nonneg hfirst hbracket

/-- **The strict numeric gap.**  The third-moment lower bound is larger than the
line-corrected upper bound whenever `h ≥ 8` and `N ≥ 2h+1`. -/
theorem upperSix_lt_lowerSix (h N : ℕ) (hh : 8 ≤ h) (hN : 2 * h + 1 ≤ N) :
    upperSix h N < lowerSix h N := by
  have hhpos : 0 < h := by omega
  have hNpos : 0 < N := by omega
  have hmono := gapQuadratic_mono_from_endpoint h N hh hN
  have hend := gapQuadratic_endpoint h hhpos
  have hhq : (0 : ℚ) < (h : ℚ) := by exact_mod_cast hhpos
  have hpoly :
      0 < 4 * (h : ℚ)^5 + 22 * (h : ℚ)^4 + 70 * (h : ℚ)^3 +
        6 * (h : ℚ)^2 + 2 * (h : ℚ) + 2 := by positivity
  have hgap0 : 0 < gapQuadratic h (2 * h + 1) := by
    have hscale : (0 : ℚ) < 8 * (h : ℚ)^2 := by positivity
    nlinarith
  have hgap : 0 < gapQuadratic h N := lt_of_lt_of_le hgap0 hmono
  have hid := lowerSix_sub_upperSix_eq h N hhpos
  have hNq : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hNpos
  nlinarith [mul_pos hNq hgap]

/-- Abstract third-moment contradiction consumer.  `T` is the actual third incidence
moment.  Geometry supplies `lowerSix ≤ 6T ≤ upperSix`; the numeric theorem rules out
`N > 2h`. -/
theorem card_le_two_mul_of_thirdMoment_bounds (h N : ℕ) (T : ℚ) (hh : 8 ≤ h)
    (hlower : lowerSix h N ≤ 6 * T)
    (hupper : 6 * T ≤ upperSix h N) :
    N ≤ 2 * h := by
  by_contra hnot
  have hN : 2 * h + 1 ≤ N := by omega
  have hgap := upperSix_lt_lowerSix h N hh hN
  linarith

/-- Pure natural-number line-size lemma used by the geometric dichotomy.  Under the
rate-`1/16` inequality and the surviving core cap, five disjoint fresh fibers do not
fit in `2h` coordinates. -/
theorem line_card_le_four {h d z L : ℕ} (hh : 8 ≤ h)
    (hrate : 8 * d + 8 ≤ h) (hcore : 2 * z + 3 ≤ h + 4 * d)
    (hcount : L * (h + 1 - z) + z ≤ 2 * h) :
    L ≤ 4 := by
  have hz : z < h + 1 := by nlinarith
  have hsub : h + 1 - z + z = h + 1 := Nat.sub_add_cancel (by omega)
  by_contra hL
  have hL5 : 5 ≤ L := by omega
  have hmul : 5 * (h + 1 - z) ≤ L * (h + 1 - z) :=
    Nat.mul_le_mul_right _ hL5
  nlinarith

/-! ## A strict beyond-half good point: `δ = 17/32` -/

/-- Six times the balanced third-moment lower bound at agreement
`t/n = 15/32`, i.e. error radius `δ = 17/32`. -/
def lowerSixSeventeenThirtyTwo (h N : ℕ) : ℚ :=
  let a : ℚ := 15 * (N : ℚ) / 32
  2 * (h : ℚ) * a * (a - 1) * (a - 2)

/-- Six times the line-corrected upper bound at rate `1/16` after the
`δ = 17/32` line-core dichotomy. -/
def upperSixSeventeenThirtyTwo (h N : ℕ) : ℚ :=
  ((h : ℚ) / 8 - 1) * (N : ℚ) * ((N : ℚ) - 1) * ((N : ℚ) - 2) +
    10 * (23 * (h : ℚ) / 32 - 1) * (N : ℚ) * ((N : ℚ) - 1)

/-- Exact positive expansion of the endpoint gap `N = 4h+1`.  Writing
`x=h-16`, every coefficient on the right is positive. -/
theorem seventeenThirtyTwo_endpoint_expansion (h : ℕ) :
    1024 * (lowerSixSeventeenThirtyTwo h (4 * h + 1) -
      upperSixSeventeenThirtyTwo h (4 * h + 1)) =
      121943055 + (678102863 / 16 : ℚ) * ((h : ℚ) - 16) +
        (20919437 / 4 : ℚ) * ((h : ℚ) - 16)^2 +
        276013 * ((h : ℚ) - 16)^3 + 5308 * ((h : ℚ) - 16)^4 := by
  simp only [lowerSixSeventeenThirtyTwo, upperSixSeventeenThirtyTwo]
  push_cast
  ring

/-- The third-moment upper bound is strictly below the balanced lower bound at
`N=4h+1`, uniformly for `h≥16`. -/
theorem upperSixSeventeenThirtyTwo_lt_lower (h : ℕ) (hh : 16 ≤ h) :
    upperSixSeventeenThirtyTwo h (4 * h + 1) <
      lowerSixSeventeenThirtyTwo h (4 * h + 1) := by
  have hhq : (16 : ℚ) ≤ (h : ℚ) := by exact_mod_cast hh
  have hx : (0 : ℚ) ≤ (h : ℚ) - 16 := sub_nonneg.mpr hhq
  have hx2 : (0 : ℚ) ≤ ((h : ℚ) - 16)^2 := sq_nonneg _
  have hx3 : (0 : ℚ) ≤ ((h : ℚ) - 16)^3 := pow_nonneg hx _
  have hx4 : (0 : ℚ) ≤ ((h : ℚ) - 16)^4 := pow_nonneg hx _
  have hexp := seventeenThirtyTwo_endpoint_expansion h
  have hpos : (0 : ℚ) <
      121943055 + (678102863 / 16 : ℚ) * ((h : ℚ) - 16) +
        (20919437 / 4 : ℚ) * ((h : ℚ) - 16)^2 +
        276013 * ((h : ℚ) - 16)^3 + 5308 * ((h : ℚ) - 16)^4 := by
    positivity
  nlinarith

/-- Abstract endpoint contradiction at `δ=17/32`.  In the RS consumer, a
hypothetical set of more than `4h=2n` bad scalars is restricted to exactly
`4h+1` points; its incidence moment would satisfy these two inequalities. -/
theorem no_thirdMoment_bounds_at_seventeenThirtyTwo (h : ℕ) (T : ℚ) (hh : 16 ≤ h)
    (hlower : lowerSixSeventeenThirtyTwo h (4 * h + 1) ≤ 6 * T)
    (hupper : 6 * T ≤ upperSixSeventeenThirtyTwo h (4 * h + 1)) :
    False := by
  have hgap := upperSixSeventeenThirtyTwo_lt_lower h hh
  linarith

/-- Natural-number line-size calculation for the `δ=17/32` geometry.  Here
`h=16m`, `n=32m`, and `t=15m`.  The surviving core cap and the rate-`1/16`
inequality force every selected affine line to contain at most twelve points. -/
theorem line_card_le_twelve_seventeenThirtyTwo {m d z L : ℕ} (hm : 1 ≤ m)
    (hrate : 8 * d + 8 ≤ 16 * m) (hcore : 2 * z ≤ 19 * m + 4 * d)
    (hcount : L * (15 * m - z) + z ≤ 32 * m) :
    L ≤ 12 := by
  have hz : z < 15 * m := by nlinarith
  have hsub : 15 * m - z + z = 15 * m := Nat.sub_add_cancel (by omega)
  by_contra hL
  have hL13 : 13 ≤ L := by omega
  have hmul : 13 * (15 * m - z) ≤ L * (15 * m - z) :=
    Nat.mul_le_mul_right _ hL13
  nlinarith

#print axioms lowerSix_sub_upperSix_eq
#print axioms gapQuadratic_endpoint
#print axioms gapQuadratic_mono_from_endpoint
#print axioms upperSix_lt_lowerSix
#print axioms card_le_two_mul_of_thirdMoment_bounds
#print axioms line_card_le_four
#print axioms seventeenThirtyTwo_endpoint_expansion
#print axioms upperSixSeventeenThirtyTwo_lt_lower
#print axioms no_thirdMoment_bounds_at_seventeenThirtyTwo
#print axioms line_card_le_twelve_seventeenThirtyTwo

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenth
