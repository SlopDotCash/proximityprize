/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankReview
import ArkLib.Research.ProximityGap.BoundedChoose
import ArkLib.Research.ProximityGap.Frontier.SmoothListPackingRadius

/-! # A parameter-only exact list cutoff for smooth evaluation domains -/

namespace ProximityPrize.RankExecutable
open FullPrizeReview ProximityGap
open scoped NNReal ENNReal

/-- Test packing at `k+2` agreements and strict failure at `k+1`. The two binomial
comparisons stop at their thresholds; the algorithm does not visit subsets or coordinates. -/
def productBoundary (n k m B : ℕ) : Boundary n :=
  let limit := (B + 1) * ((k + 2) * (k + 1) / 2)
  let required := n * B
  if 0 < k ∧ k + 1 ≤ n ∧ 0 < m ∧ BoundedChoose.capped n k limit < limit ∧
      required < BoundedChoose.capped n (k + 1) (required + 1) then
    some ⟨n - (k + 1), by omega⟩
  else none

/-- A successful parameter test computes the operational answer at every real tolerance. -/
theorem productBoundary_correct {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]
    [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) (k m : ℕ)
    {e : Fin (Fintype.card I + 1)}
    (result : productBoundary (Fintype.card I) k m (RankReview.budget F ε) = some e) :
    some e = RankReview.listAnswer D ε k m := by
  classical
  unfold productBoundary at result
  dsimp only at result
  split at result
  · rename_i h
    obtain ⟨hk, ht, hm, hi, lo⟩ := h
    rw [BoundedChoose.capped_eq, min_lt_iff] at hi
    have packed := hi.resolve_right (lt_irrefl _)
    rw [BoundedChoose.capped_eq, lt_min_iff] at lo
    have denom : (k + 2).choose k = (k + 2) * (k + 1) / 2 := by
      rw [Nat.choose_symm_add, Nat.choose_two_right]
      rfl
    rw [← denom] at packed
    have upper := (Nat.div_lt_iff_lt_mul (Nat.choose_pos (show k ≤ k + 2 by omega))).mpr packed
    cases result
    apply correctBoundary_unique Fintype.card_pos _
      (RankReview.listAnswer_correct D ε k m (by omega))
    intro δ _
    refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) (δ : ℝ) ε).trans ?_
    have spec := SmoothListPackingRadius.good_iff D (a := 0) (B := RankReview.budget F ε) hk hm
      (by simpa only [Nat.add_zero] using ht) (by simpa using lo.1)
      (Nat.le_of_lt_succ upper) (δ : ℝ)
    dsimp only
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    simpa only [Nat.add_zero, RankReview.budget] using spec
  · cases result

#print axioms productBoundary_correct
end ProximityPrize.RankExecutable
