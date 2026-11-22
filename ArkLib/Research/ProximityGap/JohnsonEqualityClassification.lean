/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JohnsonEqualityExamples
import ArkLib.Research.ProximityGap.JohnsonGridEquality
import ArkLib.Research.ProximityGap.JohnsonPrimePowerList

/-! # When an actual smooth 128-bit list threshold can equal the Johnson radius -/

namespace ProximityPrize.JohnsonEqualityExamples

open FullPrizeReview ProximityGap RankJohnsonComparison
open scoped NNReal

/-- The sixteen nonzero elements of the prime subfield in the degree-32
extension in characteristic seventeen realize the second dimension-two case. -/
theorem length_sixteen : realizable 16 2 := by
  open JohnsonPrimePowerDomain in
    refine ⟨F, Grid, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, domain, ⟨smoothDomain⟩, card_grid, field_lt, ?_⟩
  intro m hm
  let : NeZero m := ⟨hm.ne'⟩
  rw [cutoff, JohnsonPrimePowerList.list_answer m]
  norm_num [Real.sqrt_div]

/-- At a prize rate, a field below the sponsor's ceiling and a smooth domain
can realize an actual 128-bit list cutoff equal to Johnson at every positive
width exactly in dimension one, or at length four or sixteen in dimension two. -/
theorem realizable_iff {n k : ℕ} (hr : hasPrizeRate n k) :
    realizable n k ↔ k = 1 ∨ k = 2 ∧ (n = 4 ∨ n = 16) := by
  constructor
  · rintro ⟨F, I, _, _, _, _, _, D, ⟨sm⟩, card, _, equal⟩
    subst n
    have alignment := (JohnsonGridEquality.grid_alignment_iff D hr).mp
      ⟨_, equal 1 (by decide)⟩
    rcases alignment with one | ⟨rfl, square⟩
    · exact Or.inl one
    · refine Or.inr ⟨rfl, ?_⟩
      have sizes : Fintype.card I = 4 ∨ Fintype.card I = 8 ∨ Fintype.card I = 16 ∨
          Fintype.card I = 32 := by rcases hr with h | h | h | h <;> omega
      rcases sizes with h | h | h | h
      · exact Or.inl h
      · rw [h] at square
        obtain ⟨a, ha⟩ := square
        have lower : a ≤ 2 := by
          by_contra! h
          have bound := Nat.mul_self_le_mul_self h
          omega
        interval_cases a <;> omega
      · exact Or.inr h
      · rw [h] at square
        obtain ⟨a, ha⟩ := square
        have lower : a ≤ 5 := by
          by_contra! h
          have bound := Nat.mul_self_le_mul_self h
          omega
        interval_cases a <;> omega
  · rintro (rfl | ⟨rfl, rfl | rfl⟩)
    · exact dimension_one hr
    · exact length_four
    · exact length_sixteen

end ProximityPrize.JohnsonEqualityExamples
