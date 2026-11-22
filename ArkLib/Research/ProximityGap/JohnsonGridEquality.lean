/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JohnsonListBoundary

/-! # When the finite Johnson radius lies on the Hamming grid

At the four prize rates, a dyadic length forces the dimension to be a power of two.
From dimension four onward every grid boundary lies strictly to one side of Johnson.
This applies to both operational answers at every tolerance, including the all-safe case.
-/

namespace ProximityPrize.JohnsonGridEquality

open FullPrizeReview RankJohnsonComparison
open scoped NNReal

/-- A particular operational boundary equals the Johnson radius precisely when its
integer agreement count squares to the Johnson radicand. -/
theorem cutoff_eq_iff {n : ℕ} (hn : 0 < n) (d : ℕ) (answer : Boundary n) :
    (cutoff answer : ℝ) / n = 1 - Real.sqrt ((d : ℝ) / n) ↔
      (n - cutoff answer) ^ 2 = n * d := by
  rw [eq_iff_le_not_lt, ← not_lt, above_iff hn, below_iff hn]
  omega

/-- The Johnson radicand at a dyadic prize rate is square exactly in dimension one,
or in dimension two when the length itself is square. -/
theorem square_iff {n k : ℕ} (hd : ∃ s : ℕ, n = 2 ^ s) (hr : hasPrizeRate n k) :
    IsSquare (n * (k - 1)) ↔ k = 1 ∨ k = 2 ∧ IsSquare n := by
  obtain ⟨s, hs⟩ := hd
  have hdiv : k ∣ 2 ^ s := by
    rw [← hs]
    rcases hr with h | h | h | h
    all_goals rw [← h]; exact dvd_mul_left _ _
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  match j with
  | 0 => simp
  | 1 => simp
  | j + 2 =>
    have hk : 2 ^ (j + 2) = 4 * 2 ^ j := by rw [pow_add]; omega
    have hp : 0 < 2 ^ j := by positivity
    have hn : ∀ a : ℕ, a ^ 2 ≠ n * (2 ^ (j + 2) - 1) := by
      rw [hs]
      apply JohnsonListBoundary.nonsquare_pow_two
      omega
    constructor
    · rintro ⟨a, ha⟩
      exact (hn a (by simpa only [pow_two] using ha.symm)).elim
    · omega

/-- For any supplied smooth code, these are exactly the dimensions and lengths
for which *some* operational grid value can equal the finite Johnson radius. -/
theorem grid_alignment_iff {F I : Type} [Field F] [DecidableEq F] [Fintype I] [Nonempty I]
    (D : I ↪ F) [ReedSolomon.Smooth D] {k : ℕ} (hr : hasPrizeRate (Fintype.card I) k) :
    (∃ a : Boundary (Fintype.card I), (cutoff a : ℝ) / Fintype.card I =
      1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)) ↔
      k = 1 ∨ k = 2 ∧ IsSquare (Fintype.card I) := by
  let n := Fintype.card I
  have hn : 0 < n := Fintype.card_pos
  have hk : k ≤ n := by rcases hr with h | h | h | h <;> dsimp [n] <;> omega
  rw [← square_iff (ReedSolomon.Smooth.h_card_pow2 (domain := D)) hr]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨_, by simpa only [pow_two] using ((cutoff_eq_iff hn _ a).mp ha).symm⟩
  · rintro ⟨t, ht⟩
    change n * (k - 1) = t * t at ht
    have htn : t ≤ n := by
      have h := Nat.mul_le_mul_left n (show k - 1 ≤ n by omega)
      nlinarith
    let a : Boundary n := some ⟨n - t, by omega⟩
    refine ⟨a, (cutoff_eq_iff hn _ a).mpr ?_⟩
    change (n - (n - t)) ^ 2 = n * (k - 1)
    rw [Nat.sub_sub_self htn, pow_two, ← ht]

/-- At every tolerance, both operational answers on a smooth prize code with dimension
at least four are strictly below or strictly above the finite Johnson radius.
The two answers may lie on different sides. -/
theorem answers_strict {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I]
    [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) {k : ℕ} (m : ℕ) (hr : hasPrizeRate (Fintype.card I) k) (hk : 4 ≤ k) :
    let J := 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)
    let strict := fun a : Boundary (Fintype.card I) =>
      (cutoff a : ℝ) / Fintype.card I < J ∨ J < (cutoff a : ℝ) / Fintype.card I
    strict (RankReview.mcaAnswer D ε k) ∧ strict (RankReview.listAnswer D ε k m) := by
  have h (a : Boundary (Fintype.card I)) :
      (cutoff a : ℝ) / Fintype.card I ≠
        1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I) := by
    intro he
    have := (grid_alignment_iff D hr).mp ⟨a, he⟩
    omega
  exact ⟨lt_or_gt_of_ne (h _), lt_or_gt_of_ne (h _)⟩

end ProximityPrize.JohnsonGridEquality
