/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank

/-! # The real Johnson radius and the next Hamming step

With budget at least the length, the strict Johnson estimate makes the entire
Hamming cell containing the Johnson radius safe whenever that radius is between
grid points. This applies at all four eligible rates for dyadic lengths from 64
onward. The positive interval can end at the very next Hamming grid point.
-/

namespace ProximityPrize.JohnsonListBoundary

open Code ProximityGap FullPrizeReview RankJohnsonComparison
open scoped NNReal ENNReal

private theorem square_mod_four (a : ℕ) : a ^ 2 % 4 = a % 2 := by
  have h := Int.sq_emod_four (a : ℤ)
  exact_mod_cast h

/-- Multiplication by a power of two cannot turn a number congruent to three modulo four
into a square. -/
theorem nonsquare_pow_two (s u : ℕ) (hu : u % 4 = 3) :
    ∀ a : ℕ, a ^ 2 ≠ 2 ^ s * u := by
  induction s using Nat.twoStepInduction with
  | zero =>
    intro a ha
    simp only [pow_zero, one_mul] at ha
    have h := square_mod_four a
    rw [ha, hu] at h
    omega
  | one =>
    intro a ha
    simp only [pow_one] at ha
    have h := square_mod_four a
    rw [ha] at h
    omega
  | more s ih _ =>
    intro a ha
    have h : a ^ 2 = 4 * (2 ^ s * u) := by
      rw [ha, pow_add]
      ring
    have par := square_mod_four a
    rw [h] at par
    have he : a = 2 * (a / 2) := by omega
    apply ih (a / 2)
    calc (a / 2) ^ 2 = (2 * (a / 2)) ^ 2 / 4 := by ring_nf; omega
      _ = 2 ^ s * u := by rw [← he, h]; omega

variable {F I : Type} [Field F] [Fintype F] [Fintype I] [Nonempty I]

/-- The exact operational list boundary lies above Johnson if the last strictly
Johnson-safe agreement count is the ceiling of a nonintegral square root.
Every positive width is covered by the length-sized list budget. -/
theorem above_of_nonsquare (D : I ↪ F) (ε : ℝ≥0) {k m : ℕ} [NeZero m]
    (hkn : k ≤ Fintype.card I) (hB : Fintype.card I ≤ RankReview.budget F ε)
    (hns : ∀ a : ℕ, a ^ 2 ≠ Fintype.card I * (k - 1)) :
    1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I) <
      (cutoff (RankReview.listAnswer D ε k m) : ℝ) / Fintype.card I := by
  classical
  let n := Fintype.card I
  let v := n * (k - 1)
  let t := v.sqrt + 1
  have hN : 0 < n := Fintype.card_pos
  have hr : 0 < (n : ℝ) := by exact_mod_cast hN
  have hn : 0 < (n : ℝ≥0) := by exact_mod_cast hN
  have ht : t ≤ n := by
    have hh : v < n * n := Nat.mul_lt_mul_of_pos_left (by omega) hN
    exact Nat.sqrt_lt.mpr hh
  let e := n - t
  have he : (e : ℝ≥0) / n ≤ 1 := (div_le_one hn).mpr (by exact_mod_cast Nat.sub_le n t)
  have list := InterleavedListJohnsonRank.interleaved_lambda_le_length D k t m
    ((e : ℝ) / n) (by
      change (e : ℝ) / n * n < (n : ℝ) - t + 1
      rw [div_mul_cancel₀ _ hr.ne']
      dsimp only [e]
      rw [Nat.cast_sub ht]
      linarith) (Nat.lt_succ_sqrt' v)
  have safe := (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
    (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
    (((e : ℝ≥0) / n : ℝ≥0) : ℝ) ε).mpr (by
      rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
      exact list.trans (by exact_mod_cast hB))
  have next := ((RankReview.listAnswer_correct D ε k m hkn) _ he).mp safe
  apply (above_iff hN (k - 1) _).mpr
  change (n - cutoff _) ^ 2 < v
  have bound : n - cutoff (RankReview.listAnswer D ε k m) ≤ v.sqrt := by
    cases h : RankReview.listAnswer D ε k m with
    | none => simp [cutoff, n]
    | some b =>
      have hb : (e : ℝ≥0) / n < (b.val : ℝ≥0) / n := by simpa only [h] using next
      have eb : e < b.val := by exact_mod_cast (div_lt_div_iff_of_pos_right hn).mp hb
      simp only [cutoff, Option.map_some, Option.getD_some]
      dsimp only [e, t] at eb ht
      omega
  exact (Nat.pow_le_pow_left bound 2).trans_lt ((Nat.sqrt_le' v).lt_of_ne (hns _))

/-- Every supplied smooth code of length at least 64 at any eligible rate has its
operational list boundary strictly above the real Johnson radius when the list
budget is at least one block length. -/
theorem all_rates [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) {k m : ℕ} [NeZero m]
    (hr : hasPrizeRate (Fintype.card I) k) (hn : 64 ≤ Fintype.card I)
    (hB : Fintype.card I ≤ RankReview.budget F ε) :
    1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I) <
      (cutoff (RankReview.listAnswer D ε k m) : ℝ) / Fintype.card I := by
  obtain ⟨s, hs⟩ := ReedSolomon.Smooth.h_card_pow2 (domain := D)
  have hs6 : 6 ≤ s := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show s ≤ 5 by omega)
    omega
  have mult : Fintype.card I = 64 * 2 ^ (s - 6) := by
    conv_lhs => rw [hs, show s = 6 + (s - 6) by omega, pow_add]
    rfl
  have k4 : k % 4 = 0 := by rcases hr with h | h | h | h <;> omega
  apply above_of_nonsquare D ε (by rcases hr with h | h | h | h <;> omega) hB
  rw [hs]
  exact nonsquare_pow_two s (k - 1) (by rcases hr with h | h | h | h <;> omega)

end ProximityPrize.JohnsonListBoundary
