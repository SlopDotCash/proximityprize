/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankKnownDomain
import ArkLib.Research.ProximityGap.Frontier.ListBudgetOne

/-! # Comparing an exact operational boundary to the finite-length Johnson radius

For a positive-dimensional Reed–Solomon code with dimension k, put d = k−1.
Its relative minimum distance is 1−d/n, so its Johnson radius is 1−√(d/n).
The first failing count gives the operational cutoff; an all-safe answer has cutoff n/n.
Both strict comparisons with Johnson reduce to integer arithmetic.
-/

namespace ProximityPrize.RankJohnsonComparison

/-- A first failure gives its grid count, and the all-safe case gives radius one. -/
def cutoff {n : ℕ} (answer : FullPrizeReview.Boundary n) : ℕ :=
  (answer.map Fin.val).getD n

theorem cutoff_le {n : ℕ} (answer : FullPrizeReview.Boundary n) : cutoff answer ≤ n := by
  cases answer with
  | none => exact le_rfl
  | some e => exact Nat.le_of_lt_succ e.isLt

private theorem johnson_square {n d : ℕ} (hn : 0 < n) :
    ((n : ℝ) * Real.sqrt ((d : ℝ) / n)) ^ 2 = n * (d : ℝ) := by
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- The operational boundary is strictly above the Johnson radius exactly when the
squared number of required agreements at the boundary is less than n·d. -/
theorem above_iff {n : ℕ} (hn : 0 < n) (d : ℕ) (answer : FullPrizeReview.Boundary n) :
    1 - Real.sqrt ((d : ℝ) / n) < (cutoff answer : ℝ) / n ↔
      (n - cutoff answer) ^ 2 < n * d := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (cutoff answer : ℝ) ≤ n := by exact_mod_cast cutoff_le answer
  rw [lt_div_iff₀ hp]
  calc
    _ ↔ (n : ℝ) - cutoff answer < n * Real.sqrt ((d : ℝ) / n) := by
      constructor <;> intro h <;> linarith
    _ ↔ ((n : ℝ) - cutoff answer) ^ 2 < n * (d : ℝ) := by
      rw [← johnson_square hn, sq_lt_sq₀ (sub_nonneg.mpr he) (by positivity)]
    _ ↔ _ := by
      rw [← Nat.cast_sub (cutoff_le answer)]
      exact_mod_cast Iff.rfl

/-- The operational boundary is strictly below the Johnson radius exactly when n·d
is less than the squared number of required agreements. -/
theorem below_iff {n : ℕ} (hn : 0 < n) (d : ℕ) (answer : FullPrizeReview.Boundary n) :
    (cutoff answer : ℝ) / n < 1 - Real.sqrt ((d : ℝ) / n) ↔
      n * d < (n - cutoff answer) ^ 2 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (cutoff answer : ℝ) ≤ n := by exact_mod_cast cutoff_le answer
  rw [div_lt_iff₀ hp]
  calc
    _ ↔ (n : ℝ) * Real.sqrt ((d : ℝ) / n) < n - cutoff answer := by
      constructor <;> intro h <;> linarith
    _ ↔ n * (d : ℝ) < ((n : ℝ) - cutoff answer) ^ 2 := by
      rw [← johnson_square hn, sq_lt_sq₀ (by positivity) (sub_nonneg.mpr he)]
    _ ↔ _ := by
      rw [← Nat.cast_sub (cutoff_le answer)]
      exact_mod_cast Iff.rfl

open ProximityGap ProximityGap.GrandChallenges FourRateListPrime246 FullPrizeReview
open scoped NNReal

/-- On the named 128-point domain both operational cutoffs strictly exceed the
finite-length Johnson radius at every prize rate and every positive list width. -/
theorem prime246_above (k m : ℕ) (hk : hasPrizeRate (Fintype.card H) k) (hm : 0 < m) :
    let radius := 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card H)
    radius < (cutoff (RankReview.mcaAnswer domain (prizeThreshold : ℝ≥0) k) : ℝ) / Fintype.card H ∧
    radius < (cutoff (RankReview.listAnswer domain (prizeThreshold : ℝ≥0) k m) : ℝ) /
      Fintype.card H := by
  dsimp only
  obtain ⟨hM, hL⟩ := RankKnownDomain.agreesWithPrime246 k hk
  rw [above_iff Fintype.card_pos, above_iff Fintype.card_pos, hM, hL m hm]
  have cases' : k = 64 ∨ k = 32 ∨ k = 16 ∨ k = 8 := by
    rw [hasPrizeRate, card_H] at hk
    omega
  rcases cases' with rfl | rfl | rfl | rfl
  · change (Fintype.card H - 62)^2 < Fintype.card H * (64-1) ∧
        (Fintype.card H - 63)^2 < Fintype.card H * (64-1)
    rw [card_H]
    decide
  · change (Fintype.card H - Fintype.card H)^2 < Fintype.card H * (32-1) ∧
        (Fintype.card H - 97)^2 < Fintype.card H * (32-1)
    rw [card_H]
    decide
  · change (Fintype.card H - Fintype.card H)^2 < Fintype.card H * (16-1) ∧
        (Fintype.card H - 113)^2 < Fintype.card H * (16-1)
    rw [card_H]
    decide
  · change (Fintype.card H - Fintype.card H)^2 < Fintype.card H * (8-1) ∧
        (Fintype.card H - 121)^2 < Fintype.card H * (8-1)
    rw [card_H]
    decide

/-- At length at least 16 and rate at most one half, the sharp budget-one list boundary
lies strictly below the finite-length Johnson radius. This includes the rounding of the midpoint. -/
theorem budgetOne_below {n k : ℕ} (hn : 16 ≤ n) (hk : 0 < k) (hr : 2 * k ≤ n) :
    ((((n - k + 2) / 2 : ℕ) : ℝ) / n) < 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n) := by
  let e := (n - k + 2) / 2
  have he : e ≤ n := by dsimp [e]; omega
  let x : ℤ := n
  let y : ℤ := (k - 1 : ℕ)
  let z : ℤ := (n - e : ℕ)
  have h1 : 0 ≤ (2 * z-(x + y - 1)) * (2 * z+(x + y - 1)) := by
    apply mul_nonneg <;> dsimp [x, y, z, e] <;> omega
  have h2 : 0 ≤ (x - y) * (x - y - 8) := by
    apply mul_nonneg <;> dsimp [x, y] <;> omega
  have h3 : 2 * (x + y) ≤ 8 * (x - y) := by dsimp [x, y]; omega
  have h4 : x * y < z ^ 2 := by nlinarith only [h1, h2, h3]
  apply (below_iff (by omega : 0 < n) (k - 1) (some ⟨e, Nat.lt_succ_of_le he⟩)).mpr
  change n * (k - 1) < (n - e) ^ 2
  dsimp [x, y, z] at h4
  exact_mod_cast h4

/-- With integer list budget one, the worst list at the Johnson radius already
exceeds budget, over every injective domain at these lengths and rates. -/
theorem listAtJohnson_exceeds_one {I F : Type} [Fintype I] [Field F] [Finite F]
    (D : I ↪ F) (k m : ℕ) (hn : 16 ≤ Fintype.card I) (hk : 0 < k)
    (hr : 2 * k ≤ Fintype.card I) (hm : 0 < m) :
    1 < Code.Lambda (Code.interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → F)))
      (1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)) := by
  rw [← not_le, ListBudgetOne.rs_safe_iff D k m hk (by omega) hm]
  exact not_lt.mpr (budgetOne_below hn hk hr).le

#print axioms budgetOne_below
#print axioms listAtJohnson_exceeds_one
#print axioms prime246_above

end ProximityPrize.RankJohnsonComparison
