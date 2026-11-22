/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity
import ArkLib.Research.ProximityGap.Frontier.TwoParityMca

/-! # Dimension-two MCA bounds at the Johnson grid

On sixteen evaluation points, every bad scalar with five or more agreements
owns six distinct detecting triples; no other bad scalar owns those triples.
There are only 560 triples. On four evaluation points, the exact two-parity
curve has only one jump, ruling out a first failure at two errors.
-/

namespace ProximityPrize.SixteenMcaJohnson

open Code ProximityGap
open scoped NNReal ENNReal

variable {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]

omit [Nonempty I] in
open Classical in
/-- Below twelve errors, every received pair has at most 93 bad scalar labels. -/
theorem bad_count_le (D : I ↪ F) (hn : Fintype.card I = 16) (u v : I → F)
    (δ : ℝ≥0) (hδ : δ < 12 / 16) :
    (Finset.univ.filter (mcaEvent (F := F) (ReedSolomon.code D 2 : Set (I → F)) δ u v)).card
      ≤ 93 := by
  classical
  have bound := CircuitDensity.mca_count_mul_le D 2 5 δ u v (by decide) (by
    intro S hs
    rw [hn, Nat.cast_ofNat, tsub_mul, one_mul] at hs
    have small := (lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 16)).mp hδ
    have big : (4 : ℝ≥0) < S.card := lt_of_lt_of_le (lt_tsub_iff_right.mpr (by linarith)) hs
    exact_mod_cast big)
  rw [hn] at bound
  norm_num [Nat.choose] at bound
  omega

/-- An integer budget covering 93 labels makes every radius below the finite
Johnson radius safe on every sixteen-point domain, even over extension fields. -/
theorem good_below (D : I ↪ F) (hn : Fintype.card I = 16) (ε : ℝ≥0)
    (budget : 93 ≤ RankReview.budget F ε) (δ : ℝ≥0) (hδ : δ < 12 / 16) :
    epsMCA (F := F) (ReedSolomon.code D 2 : Set (I → F)) δ ≤ ε := by
  classical
  rw [SimultaneousSupportRank.epsMCA_le_iff_floor_budget]
  apply epsMCA_le_of_badCount_le
  intro u
  exact (bad_count_le D hn (u 0) (u 1) δ hδ).trans budget

/-- A strict failure at twelve errors, together with a budget of at least 93,
determines the complete rank answer. -/
theorem answer_of_failure (D : I ↪ F) (hn : Fintype.card I = 16) (ε : ℝ≥0)
    (budget : 93 ≤ RankReview.budget F ε)
    (bad : (ε : ℝ≥0∞) < epsMCA (F := F) (ReedSolomon.code D 2 : Set (I → F)) (12 / 16)) :
    (RankReview.mcaAnswer D ε 2).map Fin.val = some 12 := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let e : Fin (Fintype.card I + 1) := ⟨12, by omega⟩
  have correct := RankReview.mcaAnswer_correct D ε 2
  have known : FullPrizeReview.correctBoundary (Fintype.card I) (some e) (fun δ =>
      CoreDefinitions.mcaError (CoreDefinitions.AffineLineGenerator F) (ReedSolomon.code D 2)
        (δ : ℝ) ≤ (ε : ℝ≥0∞)) := by
    intro δ _
    change CoreDefinitions.mcaError _ _ _ ≤ _ ↔ δ < (12 : ℝ≥0) / Fintype.card I
    rw [← epsMCA_eq_mcaError, hn]
    refine ⟨fun safe => lt_of_not_ge fun crossed => ?_, good_below D hn ε budget δ⟩
    exact (bad.trans_le (epsMCA_mono _ crossed)).not_ge safe
  rw [FullPrizeReview.correctBoundary_unique Fintype.card_pos correct known]
  rfl

/-- At length four and dimension two, the MCA operational cutoff cannot be two
errors at any tolerance. This covers the all-safe and empty-safe cases as well. -/
theorem four_cutoff_ne_two (D : I ↪ F) (hn : Fintype.card I = 4) (ε : ℝ≥0) :
    RankJohnsonComparison.cutoff (RankReview.mcaAnswer D ε 2) ≠ 2 := by
  classical
  let _ : SampleableType F := SampleableType.ofFintype _
  let C : Set (I → F) := ReedSolomon.code D 2
  have Q : (1 : ℝ≥0) / 4 < 2 / 4 :=
    (div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num)
  have unit : (2 : ℝ≥0) / 4 ≤ 1 :=
    (div_le_one (by norm_num : (0 : ℝ≥0) < 4)).mpr (by norm_num)
  have same : epsMCA (F := F) C (1 / 4) = epsMCA (F := F) C (2 / 4) := by
    rw [TwoParityMca.profile D (k := 2) (by omega), TwoParityMca.profile D (k := 2) (by omega)]
    rw [hn, Nat.cast_ofNat, ite_eq_left le_rfl, ite_eq_left Q.le]
  intro eq
  cases ans : RankReview.mcaAnswer D ε 2 with
  | none => simp [ans, RankJohnsonComparison.cutoff, hn] at eq
  | some e =>
    have he : e.val = 2 := by simpa [ans, RankJohnsonComparison.cutoff] using eq
    have test (δ : ℝ≥0) (h : δ ≤ 1) : epsMCA (F := F) C δ ≤ ε ↔ δ < 2 / 4 := by
      have spec := RankReview.mcaAnswer_correct D ε 2 δ h
      simpa only [C, ans, ← epsMCA_eq_mcaError, he, hn, Nat.cast_ofNat] using spec
    have safe := (test (1 / 4) (Q.le.trans unit)).mpr Q
    rw [same] at safe
    exact (lt_irrefl _) ((test _ unit).mp safe)

end ProximityPrize.SixteenMcaJohnson
