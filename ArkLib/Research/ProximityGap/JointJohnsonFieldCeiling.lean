/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.CappedJohnsonTolerance
import ArkLib.Research.ProximityGap.Frontier.PrizeFieldCeiling

/-! # Exact tolerance for simultaneous Johnson equality under the prize field ceiling -/

namespace ProximityPrize.JointJohnsonFieldCeiling

open FullPrizeReview ProximityGap CappedJohnsonTolerance
open scoped NNReal

private theorem constant_case {n : ℕ} (hr : hasPrizeRate n 1) (ε : ℝ≥0) :
    realizable n 1 ε ↔ required n ≤ ⌊ε * (PrizeFieldCeiling.maxCard n : ℝ≥0)⌋₊ := by
  have sizes : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
    rcases hr with h | h | h | h <;> omega
  have dyad : ∃ j : ℕ, n = 2 ^ j := by
    rcases sizes with rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  let _ : Fact (PrizeFieldCeiling.maxCard n).Prime := ⟨PrizeFieldCeiling.prime n⟩
  apply at_maximal_prime hr dyad (PrizeFieldCeiling.dvd_sub_one sizes)
    (PrizeFieldCeiling.below n) (fun _ power div high =>
      PrizeFieldCeiling.upper_order sizes power div high)
  rcases sizes with rfl | rfl | rfl | rfl <;> decide

/-- At every prize rate and every supplied tolerance, this is the complete numerical
criterion for some field below the sponsor's ceiling and one smooth domain to realize
both Johnson cutoffs at every positive width. The certified prime in the denominator
is respectively 2^256 minus 189, 435, 2063 or 2063 at lengths 2, 4, 8, 16. -/
theorem realizable_iff {n k : ℕ} (hr : hasPrizeRate n k) (ε : ℝ≥0) :
    realizable n k ε ↔ k = 1 ∧
      (required n : ℝ≥0) / (PrizeFieldCeiling.maxCard n : ℝ≥0) ≤ ε := by
  have positive : (0 : ℝ≥0) < PrizeFieldCeiling.maxCard n := by
    exact_mod_cast (PrizeFieldCeiling.prime n).pos
  have test : (required n : ℝ≥0) / (PrizeFieldCeiling.maxCard n : ℝ≥0) ≤ ε ↔
      required n ≤ ⌊ε * (PrizeFieldCeiling.maxCard n : ℝ≥0)⌋₊ := by
    rw [div_le_iff₀ positive, Nat.le_floor_iff (by positivity)]
  constructor
  · intro ex
    have one : k = 1 := by
      obtain ⟨F, I, _, _, _, _, _, D, ⟨sm⟩, size, _, joint⟩ := ex
      subst n
      exact ((JointJohnsonTolerance.supplied_iff D ε hr).mp joint).1
    subst k
    exact ⟨rfl, test.mpr ((constant_case hr ε).mp ex)⟩
  · rintro ⟨rfl, fits⟩
    exact (constant_case hr ε).mpr (test.mp fits)

/-- Exact integer numerators in decreasing rate order for dimension one. -/
theorem numerators : required 2 = 2 ∧ required 4 = 6 ∧
    required 8 = 28 ∧ required 16 = 120 := by decide

end ProximityPrize.JointJohnsonFieldCeiling
