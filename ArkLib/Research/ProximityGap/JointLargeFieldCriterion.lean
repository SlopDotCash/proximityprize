/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointLargeFieldReview

/-! # The exact field-size criterion for the large-field answers at every rate

An even length supplies a half-rate code. At dimension-many agreements its exact
list size is the central binomial coefficient. This proves necessity of the
quantitative field bound for the joint all-rate answers, at every positive width.
-/

namespace ProximityPrize.JointLargeFieldCriterion
open Code ProximityGap FullPrizeReview
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- An answer at the minimum distance entails that the preceding Hamming shell
holds the entire extremal list of size `n.choose k` within budget. -/
theorem budget_of_minimum_list (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0)
    {k m : ℕ} (hk : 0 < k) [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hL : (RankReview.listAnswer D ε k m).map Fin.val = some (Fintype.card I - k + 1)) :
    (Fintype.card I).choose k ≤ RankReview.budget F ε := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k ≤ Fintype.card I := by rcases hr with h | h | h | h <;> omega
  have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hδ : ((Fintype.card I - k : ℕ) : ℝ≥0) / Fintype.card I ≤ 1 :=
    (div_le_one hn).mpr (by exact_mod_cast Nat.sub_le (Fintype.card I) k)
  have hs := (RankReview.correctForEveryDomain D ε k hr).2 m (NeZero.pos m) _ hδ
  cases he : RankReview.listAnswer D ε k m with
  | none => simp [he] at hL
  | some i =>
    have hv : i.val = Fintype.card I - k + 1 := by simpa only [he, Option.map_some,
      Option.some.injEq] using hL
    rw [he] at hs
    have hgood := hs.mpr (show ((Fintype.card I - k : ℕ) : ℝ≥0) / Fintype.card I <
        (i.val : ℝ≥0) / Fintype.card I by
      rw [div_lt_div_iff_of_pos_right hn, hv]
      exact_mod_cast Nat.lt_succ_self (Fintype.card I - k))
    have raw := (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) _ ε).mp hgood
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
      ListInterpolationBoundary.at_dimension_agreement D hk hkn (NeZero.pos m)] at raw
    exact_mod_cast raw

/-- On a positive even smooth domain, one numerical condition is necessary and
sufficient for the joint large-field values at all eligible rates at any fixed positive width. -/
theorem all_rates_iff (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) (hε : ε < 1)
    (heven : 2 ∣ Fintype.card I) (m : ℕ) [NeZero m] :
    (∀ k, hasPrizeRate (Fintype.card I) k →
      RankReview.mcaAnswer D ε k = none ∧
        (RankReview.listAnswer D ε k m).map Fin.val = some (Fintype.card I - k + 1)) ↔
      (Fintype.card I).choose (Fintype.card I / 2) ≤ RankReview.budget F ε := by
  have hn := Fintype.card_pos (α := I)
  constructor
  · intro hall
    have hr : hasPrizeRate (Fintype.card I) (Fintype.card I / 2) := Or.inl (by omega)
    exact budget_of_minimum_list (m := m) D ε (by omega) hr (hall _ hr).2
  · intro hB k hr
    have hk : 0 < k := by rcases hr with h | h | h | h <;> omega
    apply JointLargeFieldReview.rank_large_field D ε hε hk hr
    exact (max_le (Nat.choose_le_middle _ _) (Nat.choose_le_middle _ _)).trans hB

/-- At 128-bit tolerance the exact threshold in the field order is `2^128`
times the central binomial coefficient of the domain length. -/
theorem prize_size_iff (D : I ↪ F) [ReedSolomon.Smooth D] (heven : 2 ∣ Fintype.card I)
    (m : ℕ) [NeZero m] :
    (∀ k, hasPrizeRate (Fintype.card I) k →
      RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none ∧
        (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m).map Fin.val =
          some (Fintype.card I - k + 1)) ↔
      (Fintype.card I).choose (Fintype.card I / 2) * 2 ^ 128 ≤ Fintype.card F := by
  rw [all_rates_iff D _ (by norm_num [prizeThreshold]) heven m, RankExecutable.prizeBudget,
    Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)]

end ProximityPrize.JointLargeFieldCriterion
