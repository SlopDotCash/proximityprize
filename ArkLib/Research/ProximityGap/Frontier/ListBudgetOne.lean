/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Research.ProximityGap.Frontier.InterleavedListProjection
import ArkLib.Research.ProximityGap.Frontier.FourRateList128
import ArkLib.Data.CodingTheory.ListDecodability

/-! # The exact one-word list budget

A minimum-distance pair fits in a common closed Hamming ball at the first error
count where twice the radius reaches the minimum distance. Combining this midpoint
with the integer distance grid gives the exact predicate at every real radius.
-/

namespace ProximityGap.ListBudgetOne

open Code

variable {I A K : Type*} [Fintype I]

open Classical in
/-- Canonical list safety at budget one for field-valued codes of positive minimum distance. -/
theorem safe_iff [Field A] (C : Set (I → A)) (δ : ℝ) (hn : 0 < Fintype.card I)
    (hd : 0 < minDist C) :
    Lambda C δ ≤ 1 ↔ δ < (((minDist C + 1) / 2 : ℕ) : ℝ) / Fintype.card I := by
  classical
  let M : Set ℕ := {d | ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧ hammingDist a b = d}
  have hex : M.Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    change 0 < sInf M at hd
    simp [hempty] at hd
  obtain ⟨a, ha, b, hb, hab, hdist⟩ := Nat.sInf_mem hex
  change hammingDist a b = minDist C at hdist
  have hnr : (0 : ℝ) < Fintype.card I := by exact_mod_cast hn
  rw [← isUniquelyDecodable_iff_Lambda_le, isUniquelyDecodable_iff_subsingleton]
  constructor
  · intro hall
    by_contra! hδ
    obtain ⟨r, har, hbr⟩ := ArkLib.CodingTheory.UniqueDecoding.exists_center_within_half hab
    rw [hdist] at har hbr
    have hmem (v : I → A) (hv : v ∈ C) (hvr : hammingDist v r ≤ (minDist C + 1) / 2) :
        v ∈ closeCodewordsRel C r δ := by
      apply mem_closeCodewordsRel_iff.mpr
      refine ⟨hv, le_trans ?_ hδ⟩
      rw [relHammingDist_coe, hammingDist_comm]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hvr) hnr.le
    exact hab (hall r (hmem a ha har) (hmem b hb hbr))
  · intro hδ r x hx y hy
    by_contra hxy
    have hx' := mem_closeCodewordsRel_iff.mp hx
    have hy' := mem_closeCodewordsRel_iff.mp hy
    have near (v : I → A) (hv : v ∈ closeCodewordsRel C r δ) :
        hammingDist r v < (minDist C + 1) / 2 := by
      have h := (mem_closeCodewordsRel_iff.mp hv).2.trans_lt hδ
      rw [relHammingDist_coe, div_lt_div_iff_of_pos_right hnr] at h
      exact_mod_cast h
    have hlow := minDist_le_dist hx'.1 hy'.1 hxy
    have htr := hammingDist_triangle x r y
    rw [hammingDist_comm x r] at htr
    have hxnear := near x hx
    have hynear := near y hy
    omega

/-- For a positive-width RS interleaving with 1 ≤ k ≤ n, the first failing error
count equals the ceiling of (n−k+1)/2. -/
theorem rs_safe_iff [Field K] [Finite K] (D : I ↪ K) (k m : ℕ) (hk : 0 < k)
    (hkn : k ≤ Fintype.card I) (hm : 0 < m) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → K))) δ ≤ 1 ↔
      δ < (((Fintype.card I - k + 2) / 2 : ℕ) : ℝ) / Fintype.card I := by
  classical
  let _ := Fintype.ofFinite K
  let _ : Nonempty I := Fintype.card_pos_iff.mp (hk.trans_le hkn)
  let _ : NeZero k := ⟨hk.ne'⟩
  let _ : NeZero m := ⟨hm.ne'⟩
  have hdist := ReedSolomon.minDist_of_le (α := D) hkn
  have hproj := InterleavedListProjection.list_budget_iff (κ := Fin m) (ReedSolomon.code D k)
    δ 1 (show 1 ≤ Nat.card K from Nat.card_pos)
  have hs := safe_iff (ReedSolomon.code D k : Set (I → K)) δ (hk.trans_le hkn)
    (hdist ▸ by omega)
  rw [hdist] at hs
  exact hproj.trans hs

open scoped NNReal ENNReal in
/-- The exact list predicate at the literal 128-bit tolerance throughout the one-word band. -/
theorem prize_safe_iff [Field K] [Fintype K] (D : I ↪ K) (k m : ℕ) (hk : 0 < k)
    (hkn : k ≤ Fintype.card I) (hm : 0 < m) (δ : ℝ) (hB : Fintype.card K / 2 ^ 128 = 1) :
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → K))) δ : ℝ≥0∞) ≤
        ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * (Fintype.card K : ℝ≥0∞) ↔
      δ < (((Fintype.card I - k + 2) / 2 : ℕ) : ℝ) / Fintype.card I := by
  have h := FourRateList128.budget_cast (Fintype.card K)
    (Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D k : Set (I → K))) δ)
  rw [hB, Nat.cast_one] at h
  exact h.trans (rs_safe_iff D k m hk hkn hm δ)

/-- At dimension zero every interleaved list contains at most the all-zero word. -/
theorem zero_dimension_safe [Field K] (D : I ↪ K) (m : ℕ) (δ : ℝ) :
    Lambda (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 0 : Set (I → K))) δ ≤ 1 := by
  classical
  let C : Set (I → Fin m → K) := interleavedCodeSet (ReedSolomon.code D 0 : Set (I → K))
  change Lambda C δ ≤ 1
  rw [← isUniquelyDecodable_iff_Lambda_le, isUniquelyDecodable_iff_subsingleton]
  intro r x hx y hy
  funext i j
  have hzero (z : I → Fin m → K) (hz : z ∈ closeCodewordsRel
      (interleavedCodeSet (κ := Fin m) (ReedSolomon.code D 0 : Set (I → K))) r δ) :
      z i j = 0 := by
    have hrow := (mem_closeCodewordsRel_iff.mp hz).1 j
    rw [ReedSolomon.code_zero] at hrow
    exact congrFun ((Submodule.mem_bot K).mp hrow) i
  exact (hzero x hx).trans (hzero y hy).symm

end ProximityGap.ListBudgetOne

#print axioms ProximityGap.ListBudgetOne.safe_iff
#print axioms ProximityGap.ListBudgetOne.rs_safe_iff

#print axioms ProximityGap.ListBudgetOne.zero_dimension_safe
#print axioms ProximityGap.ListBudgetOne.prize_safe_iff
