/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothCapacityGap
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerListDescent

/-! # Uniform capacity gaps on smooth domains at all four prize rates

For field orders below `2^256`, the first table gives radii at which both
128-bit tests fail, and the second gives radii at which the MCA error is one
and closed lists exceed the square of the field order. Rows are ordered by
rates `1/2, 1/4, 1/8, 1/16`. Each applies at every smooth length at least
the indicated base and every positive interleaving width.
-/

namespace ProximityPrize.SmoothPrizeCapacityTable

open Code ProximityGap
open scoped NNReal ENNReal

/-- Minimum lengths for the simultaneous prize-budget failures. -/
def failureLength : Fin 4 → ℕ := ![256, 256, 256, 512]

/-- Relative radii at which both prize-budget tests fail. -/
noncomputable def failureRadius : Fin 4 → ℝ≥0 := ![127/256, 191/256, 223/256, 479/512]

/-- Minimum lengths for the error-one and list-size-square conclusions. -/
def saturationLength : Fin 4 → ℕ := ![1024, 1024, 1024, 2048]

/-- Relative radii at which MCA error reaches one and lists exceed the squared field order. -/
noncomputable def saturationRadius : Fin 4 → ℝ≥0 := ![511/1024, 767/1024, 895/1024, 1919/2048]

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

omit [Fintype F] in
/-- Write every sufficiently large smooth length as a multiple of a dyadic base while
tracking the dimension at the requested prize rate. -/
theorem dimensions (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) {h : ℕ}
    (power : ∃ b : ℕ, h = 2 ^ b) (large : h ≤ Fintype.card I) (divides : prizeDenominator i ∣ h) :
    ∃ m, 0 < m ∧ Fintype.card I = m * h ∧
      prizeDimension (ι := I) i = (h / prizeDenominator i) * m := by
  obtain ⟨b, hb⟩ := power
  obtain ⟨t, ht⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
  have exps : b ≤ t := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hb ▸ ht ▸ large)
  have dvd : h ∣ Fintype.card I := by rw [hb, ht]; exact pow_dvd_pow _ exps
  obtain ⟨m, hm⟩ := dvd
  rw [Nat.mul_comm h m] at hm
  refine ⟨m, ?_, hm, ?_⟩
  · have := Fintype.card_pos (α := I)
    by_contra! hz
    simp [show m = 0 by omega] at hm
  · rw [prizeDimension, hm, Nat.mul_div_assoc _ divides, Nat.mul_comm]

/-- The field budget is below two to the 128th power and satisfies pair separation. -/
theorem prize_budget {q : ℕ} (hpos : 0 < q) (hq : q < 2 ^ 256) :
    q / 2 ^ 128 < 2 ^ 128 ∧ (q / 2 ^ 128 + 1).choose 2 ≤ q := by
  have hb : q / 2 ^ 128 < 2 ^ 128 := by omega
  refine ⟨hb, ToleranceCircuitCriterion.pair_bound_of_square ?_⟩
  by_cases hz : q / 2 ^ 128 = 0
  · rw [hz, zero_pow (by decide : 2 ≠ 0)]
    exact hpos
  · rw [sq]
    exact (Nat.mul_lt_mul_of_pos_left hb (Nat.pos_of_ne_zero hz)).trans_le (Nat.div_mul_le_self q _)

omit [Fintype F] in
private theorem list_from_base [Finite F] (D : I ↪ F) [ReedSolomon.Smooth D] (width : ℕ)
    [NeZero width] {s j m B : ℕ} (hm : 0 < m) (hn : Fintype.card I = m * s)
    (hs : ∃ b : ℕ, s = 2 ^ b) (hj : 0 < j) (hB : s * B < s.choose (j + 1)) {δ : ℝ≥0}
    (hδ : (((s - (j + 1) : ℕ) : ℝ) / s) ≤ δ) :
    (B : ℕ∞) < Lambda (ListInterpolationBoundary.words D (j * m) width) (δ : ℝ) := by
  exact (SmoothPowerListDescent.smooth_list_exceeds (Fin width) D hm hn hs hj hB).trans_le
    (Lambda_mono hδ)

private theorem complement {h j : ℕ} (hj : j < h) :
    1 - ((j + 1 : ℕ) : ℝ≥0) / h = ((h - (j + 1) : ℕ) : ℝ≥0) / h := by
  rw [Nat.cast_tsub, tsub_div, div_self (by exact_mod_cast (show h ≠ 0 by omega))]

/-- At each row's stated radius and above, both actual 128-bit tests fail on every smooth
domain at least as large as the base. The list conclusion uses the supplied field size. -/
theorem failures (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hn : failureLength i ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    {δ : ℝ≥0} (hδ : failureRadius i ≤ δ) :
    (prizeThreshold : ℝ≥0) < epsMCA (F := F)
        ((ReedSolomon.code D (prizeDimension (ι := I) i) : Set (I → F)) ^⋈ (Fin width)) δ ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
        (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width) (δ : ℝ) :
          ℝ≥0∞) := by
  let h := failureLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 9 else 8, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn', hdim⟩ := dimensions D i hp hn (by fin_cases i <;> decide)
  obtain ⟨b, hb⟩ := hp
  obtain ⟨low, sep⟩ := prize_budget Fintype.card_pos hq
  have hj : 0 < j := by fin_cases i <;> decide
  have hjh : j < h := by fin_cases i <;> decide
  have count : h * 2 ^ 128 < h.choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have hB : h * RankReview.budget F (prizeThreshold : ℝ≥0) < h.choose (j + 1) := by
    rw [RankExecutable.prizeBudget]
    exact (Nat.mul_le_mul_left _ low.le).trans_lt count
  have eqR : ((h - (j + 1) : ℕ) : ℝ≥0) / h = failureRadius i := by
    fin_cases i <;> norm_num [h, j, failureLength, failureRadius, prizeDenominator]
  have range := eqR.trans_le hδ
  rw [hdim]
  constructor
  · apply SmoothCapacityGap.mca_from_base D _ hm hn' hb hj hjh
    · rwa [RankExecutable.prizeBudget]
    · exact (Nat.le_mul_of_pos_left _ (hj.trans hjh)).trans_lt hB
    · exact (complement hjh).trans_le range
  · apply lt_of_not_ge
    intro good
    have bound := (ListSupportRank.lambda_le_floor_iff (K := F) _ _ _).mp good
    exact (list_from_base D width hm hn' ⟨b, hb⟩ hj hB (by exact_mod_cast range)).not_ge
      bound

set_option exponentiation.threshold 512 in
/-- At the larger row cutoff the MCA probability is exactly one and the actual closed
list exceeds `q²`, uniformly across smooth larger lengths and positive widths. -/
theorem saturated (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hn : saturationLength i ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    {δ : ℝ≥0} (hδ : saturationRadius i ≤ δ) :
    epsMCA (F := F) ((ReedSolomon.code D (prizeDimension (ι := I) i) : Set (I → F)) ^⋈
        (Fin width)) δ = 1 ∧
      ((Fintype.card F ^ 2 : ℕ) : ℕ∞) <
        Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width) (δ : ℝ) := by
  let h := saturationLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 11 else 10, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn', hdim⟩ := dimensions D i hp hn (by fin_cases i <;> decide)
  obtain ⟨b, hb⟩ := hp
  have count : h * 2 ^ 512 < h.choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have field : Fintype.card F ^ 2 < 2 ^ 512 := by
    calc
      _ < (2 ^ 256 : ℕ) ^ 2 := Nat.pow_lt_pow_left hq (by decide)
      _ = 2 ^ 512 := (pow_mul (2 : ℕ) 256 2).symm
  have hjh : j < h := by fin_cases i <;> decide
  have eqR : ((h - (j + 1) : ℕ) : ℝ≥0) / h = saturationRadius i := by
    fin_cases i <;> norm_num [h, j, saturationLength, saturationRadius, prizeDenominator]
  have range := eqR.trans_le hδ
  rw [hdim]
  constructor
  · exact SmoothCapacityGap.full_from_base D hm hn' hb (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) hq ((complement hjh).trans_le range)
  · exact list_from_base D width hm hn' ⟨b, hb⟩ (by fin_cases i <;> decide)
      ((Nat.mul_le_mul_left h field.le).trans_lt count) (by exact_mod_cast range)

end ProximityPrize.SmoothPrizeCapacityTable
