/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothPrizeCapacityTable
import ArkLib.Research.ProximityGap.Frontier.SmoothReservedProductList

/-! # Uniform four-rate list cutoffs with a reserved power fiber -/

namespace ProximityPrize.SmoothReservedListBoundary

open Code ProximityGap GrandChallenges SmoothPrizeCapacityTable
open scoped NNReal ENNReal

/-- The four error coefficients for the finite-length upper bounds `r*m + 1`. -/
def errorCoefficient : Fin 4 → ℕ := ![126, 190, 222, 478]

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- On each smooth domain at least as large as the base, all positive widths exceed
the actual 128-bit list budget by `r*m+1` errors, where the length is `m*h`. -/
theorem failure (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hlen : failureLength i ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256) :
    ∃ m : ℕ, 0 < m ∧ Fintype.card I = m * failureLength i ∧
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
        (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
          (gridPt (ι := I) (errorCoefficient i * m + 1) : ℝ) : ℝ≥0∞) := by
  let h := failureLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 9 else 8, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn, hdim⟩ := dimensions D i hp hlen (by fin_cases i <;> decide)
  refine ⟨m, hm, hn, ?_⟩
  have hj : 0 < j := by fin_cases i <;> decide
  have coeff : h - j - 2 = errorCoefficient i := by fin_cases i <;> decide
  have count : h * 2 ^ 128 < (h - 1).choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have budget : h * RankReview.budget F (prizeThreshold : ℝ≥0) < (h - 1).choose (j + 1) := by
    rw [RankExecutable.prizeBudget]
    exact (Nat.mul_le_mul_left h (prize_budget Fintype.card_pos field).1.le).trans_lt count
  have bad := SmoothReservedProductList.smooth_list_exceeds (Fin width) D hm hn hp hj budget
  rw [coeff] at bad
  rw [hdim]
  apply lt_of_not_ge
  intro safe
  exact bad.not_ge ((ListSupportRank.lambda_le_floor_iff (K := F) _ _ _).mp safe)

/-- With at least two fibers per power value, a single radius suffices across all
larger lengths. In prize order these radii are 253/512, 381/512, 445/512 and 957/1024. -/
theorem longer_failure (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hlen : failureLength i < Fintype.card I) (field : Fintype.card F < 2 ^ 256) :
    ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
      (Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
        (((2 * errorCoefficient i + 1 : ℕ) : ℝ) / (2 * (failureLength i : ℝ))) : ℝ≥0∞) := by
  obtain ⟨m, hm, len, fail⟩ := failure D i width hlen.le field
  have hpos : 0 < failureLength i := by fin_cases i <;> decide
  have more : 2 ≤ m := by
    by_contra! h
    rw [show m = 1 by omega, one_mul] at len
    omega
  have radius : (gridPt (ι := I) (errorCoefficient i * m + 1) : ℝ) ≤
      ((2 * errorCoefficient i + 1 : ℕ) : ℝ) / (2 * (failureLength i : ℝ)) := by
    change ((errorCoefficient i * m + 1 : ℕ) : ℝ) / Fintype.card I ≤ _
    rw [len, div_le_div_iff₀ (by positivity) (by positivity)]
    exact_mod_cast (show (errorCoefficient i * m + 1) * (2 * failureLength i) ≤
        (2 * errorCoefficient i + 1) * (m * failureLength i) by
      nlinarith only [Nat.mul_le_mul_right (failureLength i) more])
  have bound := Lambda_mono
    (C := ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width) radius
  exact fail.trans_le (by exact_mod_cast bound)

/-- The exact finite support-rank answer is a failing Hamming step no later than
the four-rate reserved-fiber bound. -/
theorem first_failure_le (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ)
    [NeZero width] (hlen : failureLength i ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256) :
    ∃ (m : ℕ) (e : Fin (Fintype.card I + 1)), 0 < m ∧ Fintype.card I = m * failureLength i ∧
      RankReview.listAnswer D (prizeThreshold : ℝ≥0) (prizeDimension (ι := I) i) width = some e ∧
      e.val ≤ errorCoefficient i * m + 1 := by
  obtain ⟨m, hm, len, fail⟩ := failure D i width hlen field
  have room : errorCoefficient i * m + 1 ≤ Fintype.card I := by
    rw [len]
    have step : errorCoefficient i + 1 ≤ failureLength i := by fin_cases i <;> decide
    have h := Nat.mul_le_mul_right m step
    rw [Nat.add_mul, one_mul, Nat.mul_comm (failureLength i)] at h
    omega
  have cert := RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0)
    (prizeDimension (ι := I) i) width (Nat.div_le_self _ _)
    (gridPt (ι := I) (errorCoefficient i * m + 1)) (gridPt_le_one room)
  cases ans : RankReview.listAnswer D (prizeThreshold : ℝ≥0) (prizeDimension (ι := I) i) width with
  | none => rw [ans] at cert; exact (fail.not_ge (cert.mpr trivial)).elim
  | some e =>
    refine ⟨m, e, hm, len, rfl, ?_⟩
    rw [ans] at cert
    have cutoff := le_of_not_gt (fun h => fail.not_ge (cert.mpr h))
    change (e.val : ℝ≥0) / Fintype.card I ≤
      ((errorCoefficient i * m + 1 : ℕ) : ℝ≥0) / Fintype.card I at cutoff
    exact_mod_cast (div_le_div_iff_of_pos_right (show (0 : ℝ≥0) < Fintype.card I by
      exact_mod_cast Fintype.card_pos)).mp cutoff

set_option exponentiation.threshold 512 in
/-- At the larger saturation bases, the same lifted lists exceed the square of the
alphabet size. The error coefficients in prize order are 510, 766, 894 and 1918. -/
theorem exceeds_field_square (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ)
    [NeZero width] (hlen : saturationLength i ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256) :
    ∃ m : ℕ, 0 < m ∧ Fintype.card I = m * saturationLength i ∧
      ((Fintype.card F ^ 2 : ℕ) : ℕ∞) <
        Lambda (ListInterpolationBoundary.words D (prizeDimension (ι := I) i) width)
          (gridPt (ι := I) ((saturationLength i - saturationLength i / prizeDenominator i - 2) *
            m + 1) : ℝ) := by
  let h := saturationLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 11 else 10, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn, hdim⟩ := dimensions D i hp hlen (by fin_cases i <;> decide)
  refine ⟨m, hm, hn, ?_⟩
  have hj : 0 < j := by fin_cases i <;> decide
  have count : h * 2 ^ 512 < (h - 1).choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have budget : Fintype.card F ^ 2 < 2 ^ 512 :=
    (Nat.pow_lt_pow_left field (by decide : 2 ≠ 0)).trans_eq ((pow_mul (2 : ℕ) 256 2).symm)
  rw [hdim]
  exact SmoothReservedProductList.smooth_list_exceeds (Fin width) D hm hn hp hj
    ((Nat.mul_le_mul_left h budget.le).trans_lt count)

/-- An admissible rate-one-eighth instance passing at every radius strictly below
the sharp uniform cutoff can have only 256 evaluation points. -/
theorem length_of_eighth_attainment (D : I ↪ F) [ReedSolomon.Smooth D] (width : ℕ)
    [NeZero width] (hlen : 256 ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256)
    (safe : ∀ δ : ℝ≥0, δ < 223 / 256 →
      (Lambda (ListInterpolationBoundary.words D (Fintype.card I / 8) width) (δ : ℝ) : ℝ≥0∞) ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F) : Fintype.card I = 256 := by
  obtain ⟨m, hm, len, fail⟩ := failure D (2 : Fin 4) width hlen field
  change Fintype.card I = m * 256 at len
  by_contra ne
  have more : 1 < m := by omega
  apply fail.not_ge
  apply safe
  change ((222 * m + 1 : ℕ) : ℝ≥0) / Fintype.card I < 223 / 256
  rw [len, lt_div_iff₀ (by norm_num), div_mul_eq_mul_div,
    div_lt_iff₀ (by exact_mod_cast (Nat.mul_pos hm (by decide : 0 < 256)))]
  exact_mod_cast (show (222 * m + 1) * 256 < 223 * (m * 256) by omega)

end ProximityPrize.SmoothReservedListBoundary
