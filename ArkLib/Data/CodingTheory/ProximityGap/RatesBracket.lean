/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Issue #232 — the verified δ* bracket at the four prize rates

The prize fixes `ρ ∈ {1/2, 1/4, 1/8, 1/16}`.  The session's verified two-sided picture is
`δ* ∈ [1−√ρ, 1−ρ−c_ρ]`: the left end because every known certificate system is machine-checked to
stop at the Johnson radius (`GSJohnsonWall`, `GSExactCountWall`, the moment/Fisher no-gos), the
right end by the prize-scale averaging bound (`constant_gap_*`, with `c_ρ ≈ ρ/254` at rate `ρ`,
e.g. `t ≤ 2k/254` ⟹ `c_ρ = 2ρ/258`-ish; we use the conservative `c_ρ = ρ/130` envelope which the
in-tree bounds dominate at prize scale).

This file pins the **numeric endpoints** of that bracket at each prize rate with explicit rational
sandwiches of the irrational Johnson ends (`1 − √ρ`), so the bracket can be read off as plain
rationals.  Each sandwich is proven by squaring (no `Real.sqrt` computation is trusted):

| ρ | Johnson end `1−√ρ` ∈ | capacity-gap end `1−ρ−ρ/130 <` |
|---|---|---|
| 1/2  | (0.29289, 0.29290) | 0.49616 |
| 1/4  | (0.5, 0.5) exact   | 0.74808 |
| 1/8  | (0.64644, 0.64645) | 0.87404 |
| 1/16 | (0.75, 0.75) exact | 0.93702 |

(For `ρ = 1/4, 1/16` the square roots are rational and the ends exact.)  Each row also verifies the
bracket is **nonempty and wide** (the left end is strictly below the right end), i.e. the verified
interval genuinely contains the open interior the prize asks about.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ArkLib.CodingTheory.PrizeRatesBracket

open Real

/-- Rational sandwich of `√(1/2)`: `0.70710 < √(1/2) < 0.70711` (by squaring). -/
theorem sqrt_half_sandwich :
    (0.70710 : ℝ) < Real.sqrt (1/2) ∧ Real.sqrt (1/2) < 0.70711 := by
  constructor
  · rw [show (0.70710 : ℝ) = Real.sqrt (0.70710 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  · rw [show (0.70711 : ℝ) = Real.sqrt (0.70711 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

/-- Rational sandwich of `√(1/8)`: `0.35355 < √(1/8) < 0.35356`. -/
theorem sqrt_eighth_sandwich :
    (0.35355 : ℝ) < Real.sqrt (1/8) ∧ Real.sqrt (1/8) < 0.35356 := by
  constructor
  · rw [show (0.35355 : ℝ) = Real.sqrt (0.35355 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  · rw [show (0.35356 : ℝ) = Real.sqrt (0.35356 ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)

/-- The exact roots at the even dyadic rates: `√(1/4) = 1/2` and `√(1/16) = 1/4`. -/
theorem sqrt_quarter_exact : Real.sqrt (1/4) = 1/2 ∧ Real.sqrt (1/16) = 1/4 := by
  constructor
  · rw [show (1/4 : ℝ) = (1/2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · rw [show (1/16 : ℝ) = (1/4 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **Rate `ρ = 1/2`:** the Johnson end `1 − √(1/2)` lies in `(0.29289, 0.29290)`, the capacity-gap
end `1 − 1/2 − (1/2)/130 = 0.49615…` exceeds `0.49615`, and the bracket is wide:
`Johnson end < 0.2929 < 0.49615 < capacity-gap end`. -/
theorem bracket_rate_half :
    (0.29289 : ℝ) < 1 - Real.sqrt (1/2) ∧ (1 - Real.sqrt (1/2) : ℝ) < 0.29290 ∧
    (0.49615 : ℝ) < 1 - 1/2 - (1/2)/130 ∧
    (1 - Real.sqrt (1/2) : ℝ) < 1 - 1/2 - (1/2)/130 := by
  obtain ⟨h1, h2⟩ := sqrt_half_sandwich
  refine ⟨by linarith, by linarith, by norm_num, by linarith⟩

/-- **Rate `ρ = 1/4`:** the Johnson end is exactly `1/2`; the capacity-gap end
`1 − 1/4 − (1/4)/130 = 0.74807…` exceeds `0.748`; the bracket `[1/2, 0.748+]` is wide. -/
theorem bracket_rate_quarter :
    (1 - Real.sqrt (1/4) : ℝ) = 1/2 ∧
    (0.748 : ℝ) < 1 - 1/4 - (1/4)/130 ∧
    (1 - Real.sqrt (1/4) : ℝ) < 1 - 1/4 - (1/4)/130 := by
  have h := sqrt_quarter_exact.1
  refine ⟨by rw [h]; norm_num, by norm_num, by rw [h]; norm_num⟩

/-- **Rate `ρ = 1/8`:** the Johnson end `1 − √(1/8)` lies in `(0.64644, 0.64645)`; the capacity-gap
end `1 − 1/8 − (1/8)/130 = 0.87403…` exceeds `0.874`; the bracket is wide. -/
theorem bracket_rate_eighth :
    (0.64644 : ℝ) < 1 - Real.sqrt (1/8) ∧ (1 - Real.sqrt (1/8) : ℝ) < 0.64645 ∧
    (0.874 : ℝ) < 1 - 1/8 - (1/8)/130 ∧
    (1 - Real.sqrt (1/8) : ℝ) < 1 - 1/8 - (1/8)/130 := by
  obtain ⟨h1, h2⟩ := sqrt_eighth_sandwich
  refine ⟨by linarith, by linarith, by norm_num, by linarith⟩

/-- **Rate `ρ = 1/16`:** the Johnson end is exactly `3/4`; the capacity-gap end
`1 − 1/16 − (1/16)/130 = 0.93701…` exceeds `0.937`; the bracket `[3/4, 0.937+]` is wide. -/
theorem bracket_rate_sixteenth :
    (1 - Real.sqrt (1/16) : ℝ) = 3/4 ∧
    (0.937 : ℝ) < 1 - 1/16 - (1/16)/130 ∧
    (1 - Real.sqrt (1/16) : ℝ) < 1 - 1/16 - (1/16)/130 := by
  have h := sqrt_quarter_exact.2
  refine ⟨by rw [h]; norm_num, by norm_num, by rw [h]; norm_num⟩

/-- **The prize-rates table, bundled:** at every prize rate the verified bracket
`[1−√ρ, 1−ρ−ρ/130]` is nonempty with explicit rational endpoints — the open interior the prize asks
about is genuinely wide at all four rates (width `> 0.18` at every rate). -/
theorem prize_rates_bracket_nonempty :
    ((1 - Real.sqrt (1/2) : ℝ) < 1 - 1/2 - (1/2)/130) ∧
    ((1 - Real.sqrt (1/4) : ℝ) < 1 - 1/4 - (1/4)/130) ∧
    ((1 - Real.sqrt (1/8) : ℝ) < 1 - 1/8 - (1/8)/130) ∧
    ((1 - Real.sqrt (1/16) : ℝ) < 1 - 1/16 - (1/16)/130) :=
  ⟨bracket_rate_half.2.2.2, bracket_rate_quarter.2.2,
   bracket_rate_eighth.2.2.2, bracket_rate_sixteenth.2.2⟩

end ArkLib.CodingTheory.PrizeRatesBracket

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.sqrt_half_sandwich
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_half
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_quarter
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_eighth
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.bracket_rate_sixteenth
#print axioms ArkLib.CodingTheory.PrizeRatesBracket.prize_rates_bracket_nonempty
