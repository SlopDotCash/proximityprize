/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.GrandChallenges

/-!
# Elementary bounds on the ABF26 prize rates

Shared lemmas about `prizeRates j = 1 / 2^(j+1)` (`j : Fin 4`, rates `1/2, 1/4, 1/8, 1/16`).
They were previously proved verbatim in `InteriorJ1`, `LDFourRate`, `Decision` and
`MCASecondMoment`; those files now use this module (audit CW-B20-06).

* `prizeRates_le_half` — every prize rate is at most `1/2`.
* `prizeRate_floor_add_one_le` — for `2 ≤ n`, every prize degree `k_j = ⌊ρ_j n⌋` satisfies
  `k_j + 1 ≤ n`.
-/

open scoped NNReal

namespace ProximityGap

/-- Every ABF26 prize rate is at most `1/2`. -/
lemma prizeRates_le_half (j : Fin 4) : prizeRates j ≤ (1 / 2 : ℝ≥0) := by
  unfold prizeRates
  have h2 : (2 : ℝ≥0) ^ (1 : ℕ) ≤ 2 ^ (j.val + 1) :=
    pow_le_pow_right₀ one_le_two (by omega)
  rw [pow_one] at h2
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2

/-- If the evaluation domain has at least two points, each prize degree is strictly below the
block length in the form `k_j + 1 ≤ n`. -/
lemma prizeRate_floor_add_one_le {ι : Type} [Fintype ι] (j : Fin 4)
    (hn : 2 ≤ Fintype.card ι) :
    ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι := by
  set k := ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have hkr : (k : ℝ≥0) ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
    rw [hk_def]
    refine le_trans (Nat.floor_le (by positivity)) ?_
    gcongr
    exact prizeRates_le_half j
  have hcast : ((k + 1 : ℕ) : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by
    push_cast
    calc (k : ℝ≥0) + 1
        ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) + 1 := by gcongr
      _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) + (1 / 2) * (Fintype.card ι : ℝ≥0) := by
          gcongr
          calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
            _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by
                gcongr
                exact_mod_cast hn
      _ = (Fintype.card ι : ℝ≥0) := by
          rw [← add_mul]
          norm_num
  exact_mod_cast hcast

end ProximityGap

#print axioms ProximityGap.prizeRates_le_half
#print axioms ProximityGap.prizeRate_floor_add_one_le
