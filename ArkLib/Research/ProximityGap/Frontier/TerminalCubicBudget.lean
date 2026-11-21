/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import Mathlib.Tactic

/-! # Arithmetic of the terminal cubic at rate one sixteenth

The two estimates apply on opposite sides of the same polar intersection length.
The integer certificate covers the smallest population in the full field-budget interval.
-/

namespace ArkLib.ProximityGap.Frontier.TerminalCubicBudget

/-- Dimension of the weighted interpolation space with the indicated cutoffs. -/
def capacity (h b t d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (b + 1), (h + 1 - j) * (t - j * d)

/-- The complete interpolation space forces its cubic factor below the weight cutoff. -/
theorem window_dimensions :
    let t := 357913943
    let d := 67108863
    let n := 1073741824
    let h := 33554432
    let c := capacity h 5 t d - (h + 1) * n
    capacity 34 4 t d = 35 * n + 595 ∧
      c = 2251799041933257 ∧ capacity (h - 3) 2 (t - 290805099) d < c ∧
      34 * h < 1342177249 := by decide

/-- For any possible cubic weight and polar length, either the polynomial-multiplier
space has positive dimension surplus or the intrinsic jet count is small enough.
All subtractions in the geometric charges are taken in the integers. -/
theorem polar_alternatives (w g r : ℤ) (hw : w ≤ 290805098)
    (hcharge : 3*r ≤ 47*w - 78*67108863 - 8*g) :
    (40 * 195 * (123 * 40 * (7*w - 9*67108863 - 3)) <
      400000001 * (40 * (3*(w-67108863)-g) - 3*67108863)) ∨
      r ≤ 1053546217 := by
  by_cases h : g < 3*(w-67108863)-12000000
  · left
    omega
  · right
    omega

/-- Net costs, scalar resultant degrees and surviving labels for both alternatives. -/
theorem multiplier_dimensions :
    let n := 1073741824
    let m := 34
    let s := 400000000
    let μ := 64
    let r := 1053546217
    let src := capacity s 2 (μ*357913943) 67108863
    let cost := (s+1-m)*((μ-1)*r+n) + m*n*(μ*(μ+1)/2)
    cost + 428325079668489781 = src ∧
      3*s+2*m < 1342177249 - (5*m-6) ∧ 3*s+2*(m-3) < 1342177249 ∧
      268435546 < 2013265890 - 144903915 := by decide

/-- The degree, population and core-packing tests hold throughout the interval of
last-good predecessors. -/
theorem population_window (e : ℕ) (hl : 671088640 ≤ e) (hu : e ≤ 715827881) :
    2013265890 ≤ 3*(e+1)+1-34 ∧
    1342177249 ≤ 2*(e+1)+1-34 ∧
    356515842 ≤ 1073741824-e-e/512 ∧
    1073741824-3*356515842+5*67108863 < 1073741824-e ∧
    2*(e+1)+4*4128+34 < 3*(e+1)+1 ∧
    1484783598 + 4*4128+34 < 3*(e+1)+1 ∧
    1224736726 + 4*4128+34 < 3*(e+1)+1 := by omega

/-- The two adjacent Hamming rungs and the common locator fit at every budget
in the stated interval. -/
theorem adjacent_steps (B : ℕ) (hl : 2013265923 ≤ B) (hu : B ≤ 2147483648) :
    let e := B/3
    let t := 1073741824-e
    let h := (3*(t-1)+1-1073741824)/2
    671088640 ≤ e-1 ∧ e-1 ≤ 715827881 ∧ 671088641 ≤ e ∧ e ≤ 715827882 ∧
      3*e ≤ B ∧ B < 3*(e+1) ∧ h ≤ 67108864-2 ∧ 67108864 ≤ t-1 ∧
      h+3*(t-1-h) ≤ 1073741824 := by
  dsimp only
  omega

#print axioms polar_alternatives
#print axioms adjacent_steps

end ArkLib.ProximityGap.Frontier.TerminalCubicBudget
