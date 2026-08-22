/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Door (iv): the depth-4 rung of the char-0 tower-doubling ratio `Q₄` (#444)

This continues the char-0 base of Shaw's tower-doubling energy recursion after the `r = 1,2,3`
rungs in `_TowerEnergyDoublingRatioBase.lean` and `_TowerEnergyDoublingRatioBaseR3.lean`.

For the in-tree kernel-proven depth-4 char-0 energy
`E₄(μ_n) = 105n⁴ - 630n³ + 1435n² - 1155n`, writing `n = 2m` gives
`E₄(m) = 1680m⁴ - 5040m³ + 5740m² - 2310m`. The tower ratio is

`Q₄(m) = E₄(2m) / (2⁴ E₄(m))`.

The theorem below pins the exact rational form and its positive `O(1/m)` excess:

* `towerRatioFour_eq`      : exact closed form of `Q₄(m)`.
* `towerRatioFour_sub_one` : exact excess over `1`.
* `towerRatioFour_gt_one`  : the depth-4 doubled energy is strictly above the variance-adding value.
* `towerRatioFour_tendsto_one` : the char-0 base decoheres to `1` at depth 4.

## Honest status
This is still the SUP-blind char-0 / averaged base of the tower recursion. It does **not** bound the
worst-`b` thin finite-field coherence and makes no CORE, cancellation, completion, anti-concentration,
or capacity claim. Prize CORE remains open. Axiom-clean; no `sorry`. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4

/-- The char-0 depth-4 additive energy of `μ_n` after writing `n = 2m`. -/
def E4 (m : ℝ) : ℝ := 1680 * m ^ 4 - 5040 * m ^ 3 + 5740 * m ^ 2 - 2310 * m

/-- The **tower-doubling ratio at depth 4**: `Q₄(m) = E₄(2m)/(16 E₄(m))`. -/
noncomputable def towerRatioFour (m : ℝ) : ℝ := E4 (2 * m) / (16 * E4 m)

/-- The reduced denominator cubic, written in a form that is positive for `m ≥ 1`. -/
theorem den_cubic_pos {m : ℝ} (hm : 1 ≤ m) :
    0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := by
  have ht : 0 ≤ m - 1 := by linarith
  have hcube : 0 ≤ (m - 1) ^ 3 := by positivity
  nlinarith [ht, hcube]

/-- The reduced numerator of the excess is positive for `m ≥ 1`. -/
theorem excess_quad_pos {m : ℝ} (hm : 1 ≤ m) :
    0 < 96 * m ^ 2 - 164 * m + 77 := by
  have ht : 0 ≤ m - 1 := by linarith
  have hsq : 0 ≤ (m - 1) ^ 2 := sq_nonneg (m - 1)
  nlinarith [ht, hsq]

/-- The depth-4 energy itself is positive for `m ≥ 1`. -/
theorem E4_pos {m : ℝ} (hm : 1 ≤ m) : 0 < E4 m := by
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  have hden : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
  unfold E4
  nlinarith [hmpos, hden]

/-- **`Q₄(m) = (192m³ − 288m² + 164m − 33)/(8(24m³ − 72m² + 82m − 33))` exactly** for `m ≥ 1`. -/
theorem towerRatioFour_eq {m : ℝ} (hm : 1 ≤ m) :
    towerRatioFour m =
      (192 * m ^ 3 - 288 * m ^ 2 + 164 * m - 33) /
        (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33)) := by
  have hE4 : (0 : ℝ) < E4 m := E4_pos hm
  have h16 : (16 : ℝ) * E4 m ≠ 0 := by positivity
  have hc : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
  have hden : (8 : ℝ) * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33) ≠ 0 := by positivity
  rw [towerRatioFour, div_eq_div_iff h16 hden]
  unfold E4
  ring

/-- **`Q₄(m) − 1 = 3(96m² − 164m + 77)/(8(24m³ − 72m² + 82m − 33))`** for `m ≥ 1`. -/
theorem towerRatioFour_sub_one {m : ℝ} (hm : 1 ≤ m) :
    towerRatioFour m - 1 =
      3 * (96 * m ^ 2 - 164 * m + 77) /
        (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33)) := by
  have hc : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
  have hden : (8 : ℝ) * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33) ≠ 0 := by positivity
  rw [towerRatioFour_eq hm, div_sub_one hden, div_eq_div_iff hden hden]
  ring

/-- **`Q₄(m) > 1`** for `m ≥ 1`. The depth-4 char-0 doubling ratio has positive excess. -/
theorem towerRatioFour_gt_one {m : ℝ} (hm : 1 ≤ m) : 1 < towerRatioFour m := by
  have hc : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
  have hq : 0 < 96 * m ^ 2 - 164 * m + 77 := excess_quad_pos hm
  have hpos :
      0 < 3 * (96 * m ^ 2 - 164 * m + 77) /
        (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33)) := by
    positivity
  have h := towerRatioFour_sub_one hm
  linarith [h ▸ hpos]

/-- A denominator lower bound used to squeeze the exact excess by `36/m`. -/
theorem den_cubic_ge_m_cubed {m : ℝ} (hm : 1 ≤ m) :
    m ^ 3 ≤ 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := by
  have ht : 0 ≤ m - 1 := by linarith
  have hq : 0 ≤ 23 * m ^ 2 - 49 * m + 33 := by
    nlinarith [sq_nonneg (46 * m - 49)]
  nlinarith [mul_nonneg ht hq]

/-- **`Q₄(m) → 1` as `m → ∞`**. The depth-4 char-0 tower excess is `O(1/m)`. -/
theorem towerRatioFour_tendsto_one :
    Filter.Tendsto (fun m : ℝ => towerRatioFour m) Filter.atTop (nhds 1) := by
  have hev : ∀ᶠ m : ℝ in Filter.atTop,
      towerRatioFour m =
        1 + 3 * (96 * m ^ 2 - 164 * m + 77) /
          (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have := towerRatioFour_sub_one hm
    linarith
  rw [Filter.tendsto_congr' hev]
  have hpoly : Filter.Tendsto
      (fun m : ℝ => 3 * (96 * m ^ 2 - 164 * m + 77) /
        (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33))) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun m : ℝ => 36 / m) Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (36 : ℝ))).div_atTop Filter.tendsto_id
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
      have hc : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
      have hq : 0 < 96 * m ^ 2 - 164 * m + 77 := excess_quad_pos hm
      positivity
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
      have hmpos : (0 : ℝ) < m := by linarith
      have hc : 0 < 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_pos hm
      have hlow : m ^ 3 ≤ 24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33 := den_cubic_ge_m_cubed hm
      have hnum : 3 * (96 * m ^ 2 - 164 * m + 77) ≤ 288 * m ^ 2 := by
        nlinarith [hm]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlow, hnum, hmpos, sq_nonneg m]
  have hlim : Filter.Tendsto
      (fun m : ℝ =>
        1 + 3 * (96 * m ^ 2 - 164 * m + 77) /
          (8 * (24 * m ^ 3 - 72 * m ^ 2 + 82 * m - 33))) Filter.atTop (nhds (1 + 0)) :=
    Filter.Tendsto.const_add 1 hpoly
  simpa using hlim

end ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.den_cubic_pos
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.excess_quad_pos
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.E4_pos
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.towerRatioFour_eq
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.towerRatioFour_sub_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.towerRatioFour_gt_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.den_cubic_ge_m_cubed
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR4.towerRatioFour_tendsto_one
