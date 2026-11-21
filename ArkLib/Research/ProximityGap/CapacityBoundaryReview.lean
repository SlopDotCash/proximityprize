/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JointAdjacentFieldReview

/-! # Comparing the two operational answers to the capacity radius

Arnon, Boneh and Fenzi call the relative minimum distance the capacity radius.
Its error count is `n - k + 1`. Every finite MCA first failure occurs at least
two errors earlier. At tolerance below one, one binomial comparison decides
whether list decoding first fails at capacity or strictly below it.
-/

namespace ProximityPrize.CapacityBoundaryReview

open Code ProximityGap CoreDefinitions FullPrizeReview
open scoped NNReal ENNReal

variable {F I : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]

/-- Every MCA first failure lies strictly below capacity, at or before the
grid point requiring `k+1` agreements. The statement covers any tolerance. -/
theorem mca_ceiling (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0)
    {k : ℕ} (hr : hasPrizeRate (Fintype.card I) k) {e : Fin (Fintype.card I + 1)}
    (he : RankReview.mcaAnswer D ε k = some e) : e.val ≤ Fintype.card I - (k + 1) := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hkn : k < Fintype.card I := by
    have := Fintype.card_pos (α := I)
    rcases hr with h | h | h | h <;> omega
  let s := Fintype.card I - (k + 1)
  have hs : (s : ℝ≥0) / Fintype.card I ≤ 1 := (div_le_one hn).mpr (by
    exact_mod_cast Nat.sub_le (Fintype.card I) (k + 1))
  have plateau : epsMCA (F := F) (ReedSolomon.code D k : Set (I → F))
      ((s : ℝ≥0) / Fintype.card I) = epsMCA (F := F) (ReedSolomon.code D k : Set (I → F)) 1 := by
    apply epsMCA_eq_epsMCA_one_of_le_succ
    rw [tsub_mul, one_mul, div_mul_cancel₀ _ hn.ne']
    dsimp [s]
    have heq : ((Fintype.card I - (k + 1) : ℕ) : ℝ≥0) + (k + 1 : ℕ) = Fintype.card I := by
      exact_mod_cast Nat.sub_add_cancel (show k + 1 ≤ Fintype.card I by omega)
    rw [tsub_le_iff_right]
    simpa [add_comm] using heq.ge
  have good := (RankReview.correctForEveryDomain D ε k hr).1
  by_contra! h
  have step := good _ hs
  have last := good 1 le_rfl
  change mcaError (AffineLineGenerator F) (ReedSolomon.code D k) _ ≤ _ ↔ _ at step last
  simp only [he] at step last
  rw [← epsMCA_eq_mcaError] at step last
  have hgood := step.mpr (show (s : ℝ≥0) / Fintype.card I < (e.val : ℝ≥0) / Fintype.card I from
    (div_lt_div_iff_of_pos_right hn).mpr (by exact_mod_cast h))
  have hone := last.mp (plateau ▸ hgood)
  exact ((div_le_one hn).mpr (by exact_mod_cast Nat.le_of_lt_succ e.isLt)).not_gt hone

/-- A list first fails at the sponsor’s capacity radius (the minimum distance)
exactly when the budget covers `choose n k`. -/
theorem list_minimum_iff (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) (hε : ε < 1)
    {k m : ℕ} (hk : 0 < k) [NeZero m] (hr : hasPrizeRate (Fintype.card I) k) :
    (RankReview.listAnswer D ε k m).map Fin.val = some (Fintype.card I - k + 1) ↔
      (Fintype.card I).choose k ≤ RankReview.budget F ε := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k ≤ Fintype.card I := by rcases hr with h | h | h | h <;> omega
  refine ⟨JointLargeFieldCriterion.budget_of_minimum_list D ε hk hr, ?_⟩
  intro cover
  have hB : RankReview.budget F ε < Fintype.card F := by
    apply (Nat.floor_lt (by positivity)).mpr
    simpa using mul_lt_mul_of_pos_right hε (by exact_mod_cast Fintype.card_pos (α := F) :
      (0 : ℝ≥0) < Fintype.card F)
  let j : Fin (Fintype.card I + 1) := ⟨Fintype.card I - k + 1, by omega⟩
  have step : correctBoundary (Fintype.card I) (some j) (fun δ =>
      (Lambda (ListInterpolationBoundary.words D k m) (δ : ℝ) : ℝ≥0∞) ≤
        (ε : ℝ≥0∞) * Fintype.card F) := by
    intro δ _
    refine (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) (δ : ℝ) ε).trans ?_
    have h := ListInterpolationBoundary.good_iff D hk hkn (NeZero.pos m)
      ((Nat.div_le_self _ _).trans cover) hB (δ : ℝ)
    rw [ite_eq_left cover] at h
    change _ ↔ δ < (j.val : ℝ≥0) / Fintype.card I
    rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    exact h
  exact congrArg (Option.map Fin.val) (correctBoundary_unique Fintype.card_pos
    ((RankReview.correctForEveryDomain D ε k hr).2 m (NeZero.pos m)) step)

/-- When the list budget misses the binomial count, the first failure occurs
at least one error below capacity at every positive width. This includes a zero budget. -/
theorem list_ceiling (D : I ↪ F) [ReedSolomon.Smooth D] (ε : ℝ≥0) {k m : ℕ}
    (hk : 0 < k) [NeZero m] (hr : hasPrizeRate (Fintype.card I) k)
    (hB : RankReview.budget F ε < (Fintype.card I).choose k) :
    ∃ e, RankReview.listAnswer D ε k m = some e ∧ e.val ≤ Fintype.card I - k := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  have hkn : k ≤ Fintype.card I := by rcases hr with h | h | h | h <;> omega
  have hn : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  let s := Fintype.card I - k
  have hs : (s : ℝ≥0) / Fintype.card I ≤ 1 := (div_le_one hn).mpr (by
    exact_mod_cast Nat.sub_le (Fintype.card I) k)
  have bad : ¬ (Lambda (ListInterpolationBoundary.words D k m)
      (((s : ℝ≥0) / Fintype.card I : ℝ≥0) : ℝ) : ℝ≥0∞) ≤ (ε : ℝ≥0∞) * Fintype.card F := by
    intro good
    have raw := (ListSupportRank.lambda_le_floor_iff (K := F) (I := I) (A := Fin m → F)
      (ListInterpolationBoundary.words D k m) _ ε).mp good
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast,
      ListInterpolationBoundary.at_dimension_agreement D hk hkn (NeZero.pos m)] at raw
    apply hB.not_ge
    exact_mod_cast raw
  have step := (RankReview.correctForEveryDomain D ε k hr).2 m (NeZero.pos m) _ hs
  cases h : RankReview.listAnswer D ε k m with
  | none => exact False.elim (bad (step.mpr (by simp [h])))
  | some e =>
    refine ⟨e, rfl, ?_⟩
    by_contra! hlt
    apply bad
    apply step.mpr
    rw [h]
    exact (div_lt_div_iff_of_pos_right hn).mpr (by exact_mod_cast hlt)

/-- At prize tolerance in fields below the sponsor ceiling, the MCA answer is
either all-safe or at least two errors below capacity. The binomial count decides
which alternative holds independently of the evaluation points. -/
theorem prize_mca_dichotomy (D : I ↪ F) [ReedSolomon.Smooth D] {k : ℕ}
    (hk : 0 < k) (hr : hasPrizeRate (Fintype.card I) k) (hq : Fintype.card F < 2 ^ 256) :
    if (Fintype.card I).choose (k + 1) ≤ Fintype.card F / 2 ^ 128 then
      RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = none
    else ∃ e, RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k = some e ∧
      e.val ≤ Fintype.card I - (k + 1) := by
  classical
  have criterion := JointAdjacentFieldReview.mca_all_safe_iff D hk hr hq
  split_ifs with hB
  · exact criterion.mpr hB
  · cases h : RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k with
    | none => exact False.elim (hB (criterion.mp h))
    | some e => exact ⟨e, rfl, mca_ceiling D _ hr h⟩

end ProximityPrize.CapacityBoundaryReview
