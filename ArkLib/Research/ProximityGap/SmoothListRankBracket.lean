/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Research.ProximityGap.SmoothReservedListBoundary
import ArkLib.Research.ProximityGap.Frontier.MultipleOmissionJohnson

/-! # Two integer bounds on the list rank answer at the sponsor tolerance -/

set_option autoImplicit false
namespace ProximityPrize.SmoothListRankBracket

open Code ProximityGap MultipleOmissionJohnson SmoothPrizeCapacityTable
open scoped NNReal ENNReal

/-- On a sufficiently long supplied smooth domain, the 128-bit list rank answer is finite.
The first integer strictly above Johnson already passes, and the base projection supplies
an upper bound on the same first failing error count, for every positive width. -/
theorem first_failure {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F] [DecidableEq F]
    (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ) [NeZero width]
    (hn : failureLength j ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hbudget : multiple j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    ∃ e : Fin (n + 1), RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      n - agreements n k + 1 ≤ e.val ∧ e.val ≤ ⌊(n : ℝ≥0) * failureRadius j⌋₊ := by
  classical
  let n := Fintype.card I
  let k := prizeDimension (ι := I) j
  let a := n - agreements n k
  let z := (a : ℝ≥0) / (n : ℝ≥0)
  have hlarge : 256 ≤ n := by
    dsimp [n]
    exact le_trans (by fin_cases j <;> decide) hn
  have de : divisor j = prizeDenominator j := by fin_cases j <;> decide
  obtain ⟨s, hs⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
  have hden : 2 ^ (j.val + 1) ≤ 2 ^ s := by
    rw [← hs]
    have : prizeDenominator j ≤ 256 := by fin_cases j <;> decide
    exact this.trans hlarge
  have dvd : prizeDenominator j ∣ n := by
    change 2 ^ (j.val + 1) ∣ Fintype.card I
    rw [hs]
    exact pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hden)
  have hd : n = divisor j * k := by
    rw [de]
    exact (Nat.mul_div_cancel' dvd).symm
  have hak : a ≤ n := Nat.sub_le _ _
  have hnr : 0 < (n : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hz : z ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hak) hnr.le
  have hu : failureRadius j ≤ 1 := by
    fin_cases j <;> norm_num [failureRadius] <;> apply div_le_one_of_le₀ <;> norm_num
  have hc := RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0) k width
    (Nat.div_le_self n (prizeDenominator j))
  have lower := (hc z hz).mp (by
    apply (FourRateList128.budget_cast (Fintype.card F) _).mpr
    exact (four_rate_safe D j k width hd hlarge).trans (by exact_mod_cast hbudget))
  have upper := mt (hc (failureRadius j) hu).mpr
    (failures D j width hn hq (δ := failureRadius j) le_rfl).2.not_ge
  cases he : RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width with
  | none => rw [he] at upper; exact False.elim (upper trivial)
  | some e =>
    rw [he] at lower upper
    have low : (a : ℝ≥0) < (e.val : ℝ≥0) :=
      (div_lt_div_iff_of_pos_right hnr).mp lower
    have high : (e.val : ℝ≥0) ≤ failureRadius j * n :=
      (div_le_iff₀ hnr).mp (not_lt.mp upper)
    refine ⟨e, he, ?_, Nat.le_floor ?_⟩
    · exact_mod_cast Nat.succ_le_of_lt (by exact_mod_cast low : a < e.val)
    · rwa [mul_comm]

/-- The reserved fiber puts the upper endpoint at `c*m+1` on length `m*h`,
compared to the base projection's `(c+1)*m`. The improvement is strict when `m>1`. -/
theorem first_failure_reserved {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]
    [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ) [NeZero width]
    (hn : failureLength j ≤ Fintype.card I) (hq : Fintype.card F < 2 ^ 256)
    (hbudget : multiple j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    let h := failureLength j
    let c := SmoothReservedListBoundary.errorCoefficient j
    ∃ e : Fin (n + 1), RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      n - agreements n k + 1 ≤ e.val ∧ e.val ≤ c * (n / h) + 1 ∧
      (h < n → c * (n / h) + 1 < ⌊(n : ℝ≥0) * failureRadius j⌋₊) := by
  obtain ⟨e, he, hlo, -⟩ := first_failure D j width hn hq hbudget
  obtain ⟨m, f, hm, len, hf, hhi⟩ := SmoothReservedListBoundary.first_failure_le D j width hn hq
  have hfe : f = e := Option.some.inj (hf.symm.trans he)
  subst f
  have hp : 0 < failureLength j := by fin_cases j <;> decide
  have hdiv : Fintype.card I / failureLength j = m := by rw [len, Nat.mul_div_cancel _ hp]
  dsimp only
  rw [hdiv]
  refine ⟨e, he, hlo, hhi, ?_⟩
  intro hl
  have hm1 : 1 < m := by
    by_contra! h
    rw [show m = 1 by omega, one_mul] at len
    omega
  let c := SmoothReservedListBoundary.errorCoefficient j
  have hrad : failureRadius j = ((c + 1 : ℕ) : ℝ≥0) / failureLength j := by
    fin_cases j <;> norm_num [failureRadius, failureLength, c,
      SmoothReservedListBoundary.errorCoefficient]
  rw [hrad, len, Nat.cast_mul, mul_assoc, mul_comm (↑(failureLength j) : ℝ≥0) (_ / _),
    div_mul_cancel₀ _ (by exact_mod_cast hp.ne'), ← Nat.cast_mul, Nat.floor_natCast]
  change c * m + 1 < m * (c + 1)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m c]
  omega

end ProximityPrize.SmoothListRankBracket

#print axioms ProximityPrize.SmoothListRankBracket.first_failure
#print axioms ProximityPrize.SmoothListRankBracket.first_failure_reserved
