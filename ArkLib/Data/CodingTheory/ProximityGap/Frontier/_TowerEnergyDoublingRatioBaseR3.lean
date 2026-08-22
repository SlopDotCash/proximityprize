/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-!
# Door (iv): the depth-3 rung of the char-0 tower-doubling ratio `Q₃` (#444)

Companion to `_TowerEnergyDoublingRatioBase.lean` (the `r = 1, 2` rungs). This pins the
**depth-3 rung** of the char-0 base of Shaw's tower-doubling energy recursion
(`scripts/probes/_tower_energy_recursion_v1.py`, `a3f17c745`):

  `Q₃(m) := E₃(μ_{2n}) / (2³ · E₃(μ_n))`,  the doubling `μ_N → μ_{2N}` (i.e. `m → 2m`).

Using the in-tree kernel-proven char-0 depth-3 energy closed form
(`CharZeroEnergyThreeExact.B6_closed`, `E₃(μ_n) = 15n³ − 45n² + 40n = 120m³ − 180m² + 80m`):

* `towerRatioThree_eq`        : `Q₃(m) = (12m² − 9m + 2) / (2(6m² − 9m + 4))` **EXACTLY**.
* `towerRatioThree_sub_one`   : `Q₃(m) − 1 = 3(3m − 2) / (2(6m² − 9m + 4))` (exact excess).
* `towerRatioThree_gt_one`    : `Q₃(m) > 1` for `m ≥ 1`.
* `towerRatioThree_tendsto_one` : `Q₃(m) → 1` as `m → ∞` (decoherence continues at depth 3).

Numerics match Shaw's seed (`Q₃ = 2.50, 1.60, 1.23, 1.10, …` down the tower) and the in-tree energy
ladder exactly.

## Honest status (char-0 BASE rung, NOT a CORE closure)
Same scope as the `r = 1, 2` file: this is the average / char-0 (L²-averaged) doubling ratio — it
does NOT bound the worst-`b` SUP, the open thin-level char-`p` coherence (the deep BGK/Paley
wall), UNTOUCHED here. No CORE / cancellation / completion / anti-concentration / moment-saving /
capacity claim. Prize CORE stays OPEN. Axiom-clean (`propext, Classical.choice, Quot.sound`); no
`sorry`. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3

/-- The char-0 depth-3 additive energy of `μ_n` (`n = 2m`): `E₃(μ_n) = 15n³ − 45n² + 40n =
120m³ − 180m² + 80m`. In-tree this is the kernel-proven `CharZeroEnergyThreeExact.B6_closed`. -/
def E3 (m : ℝ) : ℝ := 120 * m ^ 3 - 180 * m ^ 2 + 80 * m

/-- The **tower-doubling ratio at depth 3**: `Q₃(m) = E₃(μ_{2n}) / (2³ · E₃(μ_n)) = E3 (2m) /
(8 · E3 m)`. -/
noncomputable def towerRatioThree (m : ℝ) : ℝ := E3 (2 * m) / (8 * E3 m)

/-- The depth-3 char-0 energy `E3 m = 120m³ − 180m² + 80m = 40m(3m² − ... )` is positive for `m ≥ 1`
(it factors as `40m·(3m² − ...)` with the quadratic strictly positive). -/
theorem E3_pos {m : ℝ} (hm : 1 ≤ m) : 0 < E3 m := by
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm
  unfold E3
  nlinarith [hmpos, hm, sq_nonneg (m - 1)]

/-- The denominator quadratic `6m² − 9m + 4` is strictly positive (negative discriminant `−15`),
so it never vanishes; needed to handle `Q₃`'s reduced denominator. -/
theorem den_quad_pos (m : ℝ) : 0 < 6 * m ^ 2 - 9 * m + 4 := by
  nlinarith [sq_nonneg (2 * m - 3), sq_nonneg m]

/-- **`Q₃(m) = (12m² − 9m + 2)/(2(6m² − 9m + 4))` EXACTLY** for `m ≥ 1`. Closed form of the depth-3
tower-doubling ratio at the char-0 base. -/
theorem towerRatioThree_eq {m : ℝ} (hm : 1 ≤ m) :
    towerRatioThree m = (12 * m ^ 2 - 9 * m + 2) / (2 * (6 * m ^ 2 - 9 * m + 4)) := by
  have hE3 : (0 : ℝ) < E3 m := E3_pos hm
  have h8 : (8 : ℝ) * E3 m ≠ 0 := by positivity
  have hq : (0 : ℝ) < 6 * m ^ 2 - 9 * m + 4 := den_quad_pos m
  have hden : (2 : ℝ) * (6 * m ^ 2 - 9 * m + 4) ≠ 0 := by positivity
  rw [towerRatioThree, div_eq_div_iff h8 hden]
  unfold E3
  ring

/-- **`Q₃(m) − 1 = 3(3m − 2)/(2(6m² − 9m + 4))`** for `m ≥ 1` — the EXACT depth-3 coherence excess
(positive, `O(1/m)`). -/
theorem towerRatioThree_sub_one {m : ℝ} (hm : 1 ≤ m) :
    towerRatioThree m - 1 = 3 * (3 * m - 2) / (2 * (6 * m ^ 2 - 9 * m + 4)) := by
  have hq : (0 : ℝ) < 6 * m ^ 2 - 9 * m + 4 := den_quad_pos m
  have hden : (2 : ℝ) * (6 * m ^ 2 - 9 * m + 4) ≠ 0 := by positivity
  rw [towerRatioThree_eq hm, div_sub_one hden, div_eq_div_iff hden hden]
  ring

/-- **`Q₃(m) > 1`** for `m ≥ 1`. The doubled depth-3 energy exceeds the variance-adding
value `2³·E₃` (positive coherence excess `3(3m − 2) > 0`). -/
theorem towerRatioThree_gt_one {m : ℝ} (hm : 1 ≤ m) : 1 < towerRatioThree m := by
  have hq : (0 : ℝ) < 6 * m ^ 2 - 9 * m + 4 := den_quad_pos m
  have hnum : (0 : ℝ) < 3 * (3 * m - 2) := by nlinarith [hm]
  have hpos : (0 : ℝ) < 3 * (3 * m - 2) / (2 * (6 * m ^ 2 - 9 * m + 4)) := by positivity
  have h := towerRatioThree_sub_one hm
  linarith [h ▸ hpos]

/-- **`Q₃(m) → 1` as `m → ∞`** — decoherence continues at depth 3 (seed observation at `r = 3`).
Via the exact excess `Q₃(m) − 1 = 3(3m − 2)/(2(6m² − 9m + 4)) → 0`. -/
theorem towerRatioThree_tendsto_one :
    Filter.Tendsto (fun m : ℝ => towerRatioThree m) Filter.atTop (nhds 1) := by
  have hev : ∀ᶠ m : ℝ in Filter.atTop,
      towerRatioThree m = 1 + 3 * (3 * m - 2) / (2 * (6 * m ^ 2 - 9 * m + 4)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
    have := towerRatioThree_sub_one hm
    linarith
  rw [Filter.tendsto_congr' hev]
  -- The excess `3(3m-2)/(2(6m²-9m+4))` is squeezed between `0` and `9/(2m)` for `m ≥ 1`
  -- (using `6m²-9m+4 ≥ m²`, i.e. `(5m-4)(m-1) ≥ 0`), and `9/(2m) → 0`.
  have hpoly : Filter.Tendsto
      (fun m : ℝ => 3 * (3 * m - 2) / (2 * (6 * m ^ 2 - 9 * m + 4))) Filter.atTop (nhds 0) := by
    have hsq : Filter.Tendsto (fun m : ℝ => 9 / (2 * m)) Filter.atTop (nhds 0) := by
      have hden : Filter.Tendsto (fun m : ℝ => (2 : ℝ) * m) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
      simpa using (tendsto_const_nhds (x := (9 : ℝ))).div_atTop hden
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsq
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
      have hq : (0 : ℝ) < 6 * m ^ 2 - 9 * m + 4 := den_quad_pos m
      have hnum : (0 : ℝ) ≤ 3 * (3 * m - 2) := by nlinarith
      positivity
    · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with m hm
      have hmpos : (0 : ℝ) < m := by linarith
      have hq : (0 : ℝ) < 6 * m ^ 2 - 9 * m + 4 := den_quad_pos m
      have hlow : m ^ 2 ≤ 6 * m ^ 2 - 9 * m + 4 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 5 * m - 4) (by linarith : (0 : ℝ) ≤ m - 1)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hlow, hmpos, hm, sq_nonneg m]
  have h3 : Filter.Tendsto
      (fun m : ℝ => 1 + 3 * (3 * m - 2) / (2 * (6 * m ^ 2 - 9 * m + 4))) Filter.atTop
      (nhds (1 + 0)) := Filter.Tendsto.const_add 1 hpoly
  simpa using h3

end ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.E3_pos
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.den_quad_pos
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.towerRatioThree_eq
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.towerRatioThree_sub_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.towerRatioThree_gt_one
#print axioms ProximityGap.Frontier.TowerEnergyDoublingRatioBaseR3.towerRatioThree_tendsto_one
