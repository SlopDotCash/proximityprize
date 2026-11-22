/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothPrizeCapacityTable
import ArkLib.Research.ProximityGap.Frontier.PuncturedSmoothMca

/-! # Finite-length MCA bounds at the four prize rates

For length `n=m*h`, denominator `d`, and base dimension `j=h/d`, the bad
radius is `((h-j-2)m+1)/n`. At the old base cutoff this is the same radius;
at a strict multiple it moves the guaranteed failure earlier by `m-1` errors.
-/

namespace ProximityPrize.SmoothReservedMcaBoundary

open Code ProximityGap GrandChallenges SmoothPrizeCapacityTable
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- Number of errors at the reserved-fiber boundary for length `n`, base `h`,
and rate `1/d`. -/
def errorCount (h d n : ℕ) : ℕ := (h - (h / d + 2)) * (n / h) + 1

private theorem grid {h d m : ℕ} (hn : Fintype.card I = m * h) (hm : 0 < m)
    (hd : h / d + 2 ≤ h) :
    1 - (((h / d + 2) * m - 1 : ℕ) : ℝ≥0) / Fintype.card I =
      gridPt (ι := I) (errorCount h d (Fintype.card I)) := by
  have base : 0 < h / d + 2 := Nat.zero_lt_succ _
  have hpos : 0 < h := base.trans_le hd
  have npos : (Fintype.card I : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have a : 0 < (h / d + 2) * m := Nat.mul_pos base hm
  have sum := Nat.sub_add_cancel hd
  have total : (h - (h / d + 2)) * m + (h / d + 2) * m = Fintype.card I := by
    rw [← Nat.add_mul, sum, hn, Nat.mul_comm]
  have count : Fintype.card I - ((h / d + 2) * m - 1) = errorCount h d (Fintype.card I) := by
    unfold errorCount
    rw [show Fintype.card I / h = m by rw [hn, Nat.mul_div_cancel _ hpos]]
    omega
  conv_rhs => rw [gridPt, ← count, Nat.cast_tsub, tsub_div, div_self npos]

/-- All four 128-bit MCA tests fail by the finite-length reserved-fiber step.
The coefficients `h-j-2` in rate order are 126, 190, 222, and 478. -/
theorem failure (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hlen : failureLength i ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256)
    {δ : ℝ≥0} (hδ : gridPt (ι := I)
      (errorCount (failureLength i) (prizeDenominator i) (Fintype.card I)) ≤ δ) :
    (prizeThreshold : ℝ≥0) < epsMCA (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) i) : Set (I → F)) ^⋈ (Fin width)) δ := by
  let h := failureLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 9 else 8, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn, hdim⟩ := dimensions D i hp hlen (by fin_cases i <;> decide)
  obtain ⟨low, sep⟩ := prize_budget Fintype.card_pos field
  have count : 2 ^ 128 < (h - 1).choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  rw [hdim]
  apply PuncturedSmoothMca.failure D _ hn hm (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
  · rwa [RankExecutable.prizeBudget]
  · rw [RankExecutable.prizeBudget]
    exact low.trans count
  · exact (grid (d := prizeDenominator i) hn hm (by fin_cases i <;> decide)).trans_le hδ

set_option exponentiation.threshold 512 in
/-- On every larger row of the saturation table, a single line makes every
scalar bad by the finite-length step. The coefficients are 510, 766, 894,
and 1918 for the four successive rates. -/
theorem saturated (D : I ↪ F) [ReedSolomon.Smooth D] (i : Fin 4) (width : ℕ) [NeZero width]
    (hlen : saturationLength i ≤ Fintype.card I) (field : Fintype.card F < 2 ^ 256)
    {δ : ℝ≥0} (hδ : gridPt (ι := I)
      (errorCount (saturationLength i) (prizeDenominator i) (Fintype.card I)) ≤ δ) :
    epsMCA (F := F)
      ((ReedSolomon.code D (prizeDimension (ι := I) i) : Set (I → F)) ^⋈ (Fin width)) δ = 1 := by
  let h := saturationLength i
  let j := h / prizeDenominator i
  have hp : ∃ b : ℕ, h = 2 ^ b := ⟨if i = 3 then 11 else 10, by fin_cases i <;> decide⟩
  obtain ⟨m, hm, hn, hdim⟩ := dimensions D i hp hlen (by fin_cases i <;> decide)
  have count : 2 ^ 512 < (h - 1).choose (j + 1) := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    fin_cases i <;> (set_option maxRecDepth 8192 in decide)
  have qbound : Fintype.card F ^ 2 < 2 ^ 512 := by
    simpa only [← pow_mul] using Nat.pow_lt_pow_left field (by decide : 2 ≠ 0)
  rw [hdim]
  apply PuncturedSmoothMca.saturated D hn hm (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) _ ((grid (d := prizeDenominator i) hn hm
      (by fin_cases i <;> decide)).trans_le hδ)
  exact (Nat.pow_le_pow_left (Nat.sub_le _ _) 2).trans_lt (qbound.trans count)

/-- Exact evaluations of the uniform MCA error-count bounds at length `2^30`
in order of decreasing rate. -/
theorem production_counts (i : Fin 4) :
    errorCount (failureLength i) (prizeDenominator i) (2 ^ 30) =
      ![528482305, 796917761, 931135489, 1002438657] i ∧
    errorCount (saturationLength i) (prizeDenominator i) (2 ^ 30) =
      ![534773761, 803209217, 937426945, 1005584385] i := by
  fin_cases i <;> decide

end ProximityPrize.SmoothReservedMcaBoundary
