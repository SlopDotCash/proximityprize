/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoParityMca
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonRank
import ArkLib.Research.ProximityGap.Frontier.ListInterpolationBoundary
import ArkLib.Research.ProximityGap.Frontier.BoundarySecurityBudget

/-! # Both prize cutoffs for a Reed–Solomon code with two parity checks

One error admits unique decoding. At two errors every pair of omitted sites
gives a distinct codeword at a suitable center. At three errors the list
exceeds every budget below the field order.
-/

set_option autoImplicit false
open Code Finset
open scoped NNReal ENNReal
namespace ProximityGap.TwoParityPrize

variable {I F : Type} [Fintype I] [Nonempty I] [DecidableEq I]
    [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Before two errors, two distinct list members would agree with each other
on at least k sites and hence represent the same interleaved codeword. -/
theorem unique (D : I ↪ F) {k : ℕ} (hk : 0 < k) (hn : Fintype.card I = k + 2)
    (m : ℕ) {δ : ℝ} (hδ : δ < 2 / (Fintype.card I : ℝ)) :
    Lambda (ListInterpolationBoundary.words D k m) δ ≤ 1 := by
  have pos : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  apply InterleavedListJohnsonRank.interleaved_lambda_le_of_block_bound D k (k + 1) m 1
  · have h := (lt_div_iff₀ pos).mp hδ
    have hn' : (Fintype.card I : ℝ) = (k : ℝ) + 2 := by exact_mod_cast hn
    rw [hn'] at h ⊢
    push_cast
    linarith
  · intro M S size overlaps
    by_contra! many
    let a : Fin M := ⟨0, by omega⟩
    let b : Fin M := ⟨1, by omega⟩
    have bound := overlaps (show a ≠ b by intro h; have := congrArg Fin.val h; simp [a, b] at this)
    have h := card_union_add_card_inter (S a) (S b)
    have u := card_le_univ (S a ∪ S b)
    rw [size, size] at h
    omega

/-- Every real radius in the list challenge, for arbitrary natural budget below
the field order and every positive interleaving width. -/
theorem list_good_iff (D : I ↪ F) {k m B : ℕ} (hk : 0 < k) (hn : Fintype.card I = k + 2)
    (hm : 0 < m) (hB : B < Fintype.card F) {δ : ℝ} (hδ : 0 ≤ δ) :
    Lambda (ListInterpolationBoundary.words D k m) δ ≤ (B : ℕ∞) ↔
      0 < B ∧ δ < (if (Fintype.card I).choose 2 ≤ B then 3 else 2) / (Fintype.card I : ℝ) := by
  have hk' : k ≤ Fintype.card I := by omega
  have choose : (Fintype.card I).choose k = (Fintype.card I).choose 2 :=
    Nat.choose_symm_of_eq_add hn
  by_cases hz : B = 0
  · subst B
    let w : I → Fin m → F := 0
    have hw : w ∈ ListInterpolationBoundary.words D k m := fun _ => (ReedSolomon.code D k).zero_mem
    have fits : ({w} : Set (I → Fin m → F)) ⊆ closeCodewordsRel (ListInterpolationBoundary.words D k m) w δ := by
      apply Set.singleton_subset_iff.mpr
      refine mem_closeCodewordsRel_iff.mpr ⟨hw, ?_⟩
      unfold Code.relHammingDist
      rw [hammingDist_self]
      simpa using hδ
    have lower : (1 : ℕ∞) ≤ Lambda (ListInterpolationBoundary.words D k m) δ := by
      calc
        (1 : ℕ∞) = ({w} : Set (I → Fin m → F)).encard := (Set.encard_singleton w).symm
        _ ≤ _ := encard_le_Lambda_of_subset_closeCodewordsRel fits
    simp only [Nat.cast_zero, lt_self_iff_false, false_and, iff_false]
    exact not_le_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ∞) < 1) lower)
  have bp : 0 < B := Nat.pos_of_ne_zero hz
  rw [and_iff_right bp]
  by_cases covers : (Fintype.card I).choose 2 ≤ B
  · have hpack := (Nat.div_le_self ((Fintype.card I).choose k) (k + 1)).trans (choose ▸ covers)
    have good := ListInterpolationBoundary.good_iff D hk hk' hm hpack hB δ
    simpa [choose, covers, show Fintype.card I - k = 2 by omega] using good
  · rw [ite_eq_right covers]
    constructor
    · contrapose!
      intro bad
      have size := ListInterpolationBoundary.at_dimension_agreement D hk hk' hm
      rw [show Fintype.card I - k = 2 by omega, choose] at size
      have hlt : (B : ℕ∞) < ((Fintype.card I).choose 2 : ℕ) := by exact_mod_cast Nat.lt_of_not_ge covers
      apply (hlt.trans_eq size.symm).trans_le
      exact Lambda_mono (by simpa using bad)
    · intro small
      exact (unique D hk hn m small).trans (by exact_mod_cast bp)

/-- Both sponsor inequalities at 128-bit tolerance, on any supplied domain
with two parity checks and at every positive interleaving width. -/
theorem at_prize_tolerance (D : I ↪ F) {k m : ℕ} (hk : 0 < k)
    (hn : Fintype.card I = k + 2) [NeZero m] (δ : ℝ≥0) :
    let B := Fintype.card F / 2 ^ 128
    (epsMCA (F := F) ((ReedSolomon.code D k : Set (I → F)) ^⋈ (Fin m)) δ ≤
      1 / (2 : ℝ≥0∞)^128 ↔ 0 < B ∧ (δ < 1 / (Fintype.card I : ℝ≥0) ∨ Fintype.card I ≤ B)) ∧
    ((Lambda (ListInterpolationBoundary.words D k m) (δ : ℝ) : ℝ≥0∞) ≤
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F ↔
      0 < B ∧ (δ : ℝ) < (if (Fintype.card I).choose 2 ≤ B then 3 else 2) / (Fintype.card I : ℝ)) := by
  dsimp only
  constructor
  · rw [TwoParityMca.interleaved_profile D hn]
    have ratio (a : ℕ) :
        (a : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) ≤ 1 / (2 : ℝ≥0∞)^128 ↔ a ≤ Fintype.card F / 2 ^ 128 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        BoundarySecurityBudget.count_ratio_le_iff (a := a) Fintype.card_pos (by decide : 0 < 2 ^ 128)
    split_ifs with h
    · rw [ratio]
      simp only [not_lt.mpr h, false_or]
      omega
    · have atOne := ratio 1
      simp only [Nat.cast_one] at atOne
      rw [atOne]
      rw [or_iff_left_of_imp (fun _ => lt_of_not_ge h), and_iff_left (lt_of_not_ge h)]
      omega
  · rw [FourRateList128.budget_cast]
    exact list_good_iff D hk hn (NeZero.pos m) (Nat.div_lt_self Fintype.card_pos (by decide)) δ.coe_nonneg

#print axioms list_good_iff
#print axioms at_prize_tolerance
end ProximityGap.TwoParityPrize
