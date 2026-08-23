/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Family
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# 1.5-Johnson Regime Geometry

Small real-analysis and distance-normalization facts for the GKL24/BGKS20 1.5-Johnson bounds in
`CapacityBounds.lean`.

The paper-side denominator contains

`(1 - δ_min + η)^(1/3) - (1 - δ_min + η)^(1/2)`.

This file isolates the regime facts that make that denominator strictly positive. It deliberately
does not touch the hot `CapacityBounds.lean` statement file; downstream reducers can import these
lemmas when threading the actual T4.11 front doors.
-/

namespace CodingTheory

/-- **GKL24 1.5-Johnson regime, lower bracket.** With `x := 1 - δ_min + η`,
positivity of the base follows from `δ_min ≤ 1` and positive slack. -/
lemma gkl24_1_5_johnson_base_pos {δ_min η : ℝ}
    (hδ_min_le : δ_min ≤ 1) (hη : 0 < η) :
    0 < 1 - δ_min + η := by
  linarith

/-- **GKL24 1.5-Johnson regime, upper bracket.** With `x := 1 - δ_min + η`,
the base is `< 1` when the slack stays below the relative minimum distance. -/
lemma gkl24_1_5_johnson_base_lt_one {δ_min η : ℝ} (hη_lt : η < δ_min) :
    1 - δ_min + η < 1 := by
  linarith

/-- For `0 < x < 1`, the cube-root exponent gives a strictly larger value than the square-root
exponent. -/
lemma rpow_cbrt_lt_sqrt_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ ((1 : ℝ) / 2) < x ^ ((1 : ℝ) / 3) :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 (by norm_num)

/-- **GKL24 1.5-Johnson denominator positivity, base form.** For `0 < x < 1`,
`x^(1/3) - x^(1/2)` is strictly positive. -/
lemma gkl24_1_5_johnson_denom_pos_of_base {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < x ^ ((1 : ℝ) / 3) - x ^ ((1 : ℝ) / 2) := by
  have hlt := rpow_cbrt_lt_sqrt_of_lt_one hx0 hx1
  linarith

/-- **GKL24 1.5-Johnson denominator positivity, regime form.** In the standard regime
`δ_min ≤ 1`, `0 < η`, and `η < δ_min`, the denominator is strictly positive. -/
lemma gkl24_1_5_johnson_denom_pos {δ_min η : ℝ}
    (hδ_min_le : δ_min ≤ 1) (hη : 0 < η) (hη_lt : η < δ_min) :
    0 < (1 - δ_min + η) ^ ((1 : ℝ) / 3)
        - (1 - δ_min + η) ^ ((1 : ℝ) / 2) :=
  gkl24_1_5_johnson_denom_pos_of_base
    (gkl24_1_5_johnson_base_pos hδ_min_le hη)
    (gkl24_1_5_johnson_base_lt_one hη_lt)

/-- The normalized minimum distance `Code.minDist C / |ι|` is at most `1` whenever the domain is
nonempty. This is the small bridge from the public T4.11 hypothesis
`δ_min = Code.minDist C / |ι|` to the denominator-regime lemma above. -/
lemma relative_minDist_le_one
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α]
    (C : ListDecodable.Code ι α) :
    (Code.minDist C : ℝ) / Fintype.card ι ≤ 1 := by
  have hcard_pos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_one hcard_pos]
  exact_mod_cast JohnsonBound.minDist_le_card C

/-- If `δ_min` is presented as normalized minimum distance, it satisfies the upper bracket
`δ_min ≤ 1`. -/
lemma δMin_le_one_of_minDist_eq
    {ι : Type} [Fintype ι] [Nonempty ι]
    {α : Type} [DecidableEq α]
    (C : ListDecodable.Code ι α) {δ_min : ℝ}
    (hδ_min : δ_min = (Code.minDist C : ℝ) / Fintype.card ι) :
    δ_min ≤ 1 := by
  rw [hδ_min]
  exact relative_minDist_le_one C

#print axioms CodingTheory.gkl24_1_5_johnson_base_pos
#print axioms CodingTheory.gkl24_1_5_johnson_base_lt_one
#print axioms CodingTheory.rpow_cbrt_lt_sqrt_of_lt_one
#print axioms CodingTheory.gkl24_1_5_johnson_denom_pos_of_base
#print axioms CodingTheory.gkl24_1_5_johnson_denom_pos
#print axioms CodingTheory.relative_minDist_le_one
#print axioms CodingTheory.δMin_le_one_of_minDist_eq

end CodingTheory
