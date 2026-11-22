/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointDyadicCeilings
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.Frontier.BudgetOneProduction

/-! # Actual list thresholds on the Johnson grid at 128-bit tolerance -/

namespace ProximityPrize.JohnsonEqualityExamples

open Code FullPrizeReview ProximityGap RankJohnsonComparison
open scoped NNReal ENNReal

/-- One supplied field and smooth domain attain the finite Johnson radius
at the sponsor's tolerance simultaneously at all positive list widths. -/
def realizable (n k : ℕ) : Prop :=
  ∃ (F I : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : Fintype I)
    (_ : Nonempty I) (D : I ↪ F), Nonempty (ReedSolomon.Smooth D) ∧
      Fintype.card I = n ∧ Fintype.card F < 2 ^ 256 ∧ ∀ m : ℕ, 0 < m →
        (cutoff (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m) : ℝ) / n =
          1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n)

/-- In dimension one the Johnson radius is one. The BLS field realizes it
as the first list failure on each of the four eligible lengths. -/
theorem dimension_one {n : ℕ} (hr : hasPrizeRate n 1) : realizable n 1 := by
  have sizes : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
    rcases hr with h | h | h | h <;> omega
  have hn : 0 < n := by omega
  have : NeZero n := ⟨hn.ne'⟩
  have dyad : ∃ s : ℕ, n = 2 ^ s := by
    rcases sizes with rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  obtain ⟨D, sm, joint⟩ := JointDyadicCeilings.bls_realizes hr dyad (Or.inl (by omega))
  refine ⟨ZMod BlsScalarSubgroup.P, Fin n, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, D, sm, Fintype.card_fin n, ?_, ?_⟩
  · rw [ZMod.card]
    decide
  · intro m hm
    let : NeZero m := ⟨hm.ne'⟩
    have h := (joint m).2
    simp only [Fintype.card_fin] at h
    rw [cutoff, h]
    simp [Nat.sub_add_cancel hn, hn.ne']

/-- At length four over the budget-one production field the first list failure
is two errors, exactly the finite Johnson radius for dimension two. -/
theorem length_four : realizable 4 2 := by
  let F := ZMod BudgetOneProduction.p
  obtain ⟨D, sm⟩ := SmoothPowerMcaDescent.exists_prime_domain
    (p := BudgetOneProduction.p) (n := 4) (by decide) ⟨2, rfl⟩
  refine ⟨F, Fin 4, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, D, sm, Fintype.card_fin 4, ?_, ?_⟩
  · change Fintype.card (ZMod BudgetOneProduction.p) < 2 ^ 256
    rw [ZMod.card]
    decide
  · intro m hm
    have b : RankReview.budget F (prizeThreshold : ℝ≥0) = 1 := by
      rw [RankExecutable.prizeBudget]
      change Fintype.card (ZMod BudgetOneProduction.p) / 2 ^ 128 = 1
      rw [ZMod.card]
      decide
    let e : Fin (Fintype.card (Fin 4) + 1) := ⟨2, by decide⟩
    have h : some e = RankReview.listAnswer D (prizeThreshold : ℝ≥0) 2 m := by
      apply RankExecutable.packingBoundary_correct
      change RankExecutable.packingBoundary _ 2 _ m (RankReview.budget F _) = some e
      rw [b]
      simp [RankExecutable.packingBoundary, hm, e]
    rw [← h]
    norm_num [cutoff, e, Real.sqrt_div]

end ProximityPrize.JohnsonEqualityExamples
