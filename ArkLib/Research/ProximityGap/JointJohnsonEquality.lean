/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.JohnsonEqualityClassification
import ArkLib.Research.ProximityGap.SixteenJohnsonSeparation
import ArkLib.Research.ProximityGap.SixteenMcaJohnson

/-! # Which smooth codes can realize the Johnson radius for both grand challenges? -/

namespace ProximityPrize.JointJohnsonEquality

open FullPrizeReview ProximityGap RankJohnsonComparison
open scoped NNReal ENNReal

/-- Some supplied smooth prize code has MCA cutoff equal to Johnson. When
`withLists` is true, the same field and domain must also realize equality
for the list cutoff simultaneously at every positive interleaving width. -/
def realizable (n k : ℕ) (withLists : Bool) : Prop :=
  ∃ (F I : Type) (_ : Field F) (_ : Fintype F) (_ : DecidableEq F) (_ : Fintype I)
    (_ : Nonempty I) (D : I ↪ F), Nonempty (ReedSolomon.Smooth D) ∧
      Fintype.card I = n ∧ Fintype.card F < 2 ^ 256 ∧
        (cutoff (RankReview.mcaAnswer D (prizeThreshold : ℝ≥0) k) : ℝ) / n =
          1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n) ∧
        (withLists = true → ∀ m : ℕ, 0 < m →
          (cutoff (RankReview.listAnswer D (prizeThreshold : ℝ≥0) k m) : ℝ) / n =
            1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n))

/-- On the BLS scalar field in dimension one, MCA is safe through one and the list
first fails at one. Both operational cutoffs equal Johnson. -/
theorem dimension_one {n : ℕ} (hr : hasPrizeRate n 1) (withLists : Bool) :
    realizable n 1 withLists := by
  have sizes : n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 := by
    rcases hr with h | h | h | h <;> omega
  have hn : 0 < n := by omega
  let _ : NeZero n := ⟨hn.ne'⟩
  have dyad : ∃ s : ℕ, n = 2 ^ s := by
    rcases sizes with rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  obtain ⟨D, sm, joint⟩ := JointDyadicCeilings.bls_realizes hr dyad (Or.inl (by omega))
  refine ⟨ZMod BlsScalarSubgroup.P, Fin n, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, D, sm, Fintype.card_fin n, ?_, ?_, ?_⟩
  · rw [ZMod.card]
    decide
  · rw [(joint 1).1]
    simp [cutoff, hn.ne']
  · intro _ m hm
    let _ : NeZero m := ⟨hm.ne'⟩
    have list := (joint m).2
    simp only [Fintype.card_fin] at list
    rw [cutoff, list]
    simp [Nat.sub_add_cancel hn, hn.ne']

/-- For every tolerance, the four-point dimension-two code is excluded from the
MCA grid equalities. This leaves dimension one and the sixteen-point case. -/
theorem mca_parameters {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) {k : ℕ} (hr : hasPrizeRate (Fintype.card I) k)
    (mca : (cutoff (RankReview.mcaAnswer D ε k) : ℝ) / Fintype.card I =
      1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)) :
    k = 1 ∨ k = 2 ∧ Fintype.card I = 16 := by
  rcases JohnsonEqualityExamples.parameters_of_grid D hr _ mca with one | ⟨rfl, four | sixteen⟩
  · exact Or.inl one
  · have h := SixteenMcaJohnson.four_cutoff_ne_two D four ε
    have size : (Fintype.card I : ℝ) = 4 := by exact_mod_cast four
    rw [size] at mca
    norm_num [Real.sqrt_div] at mca
    exact False.elim (h (by exact_mod_cast (show
      (cutoff (RankReview.mcaAnswer D ε 2) : ℝ) = 2 by linarith)))
  · exact Or.inr ⟨rfl, sixteen⟩

/-- If both cutoffs equal Johnson on a single smooth input at the supplied
tolerance and list width, then its Reed–Solomon dimension is one. -/
theorem dimension_one_of_both {I F : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype I] [Nonempty I] (D : I ↪ F) [ReedSolomon.Smooth D]
    (ε : ℝ≥0) {k : ℕ} (hr : hasPrizeRate (Fintype.card I) k) (m : ℕ)
    (mca : (cutoff (RankReview.mcaAnswer D ε k) : ℝ) / Fintype.card I =
      1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I))
    (list : (cutoff (RankReview.listAnswer D ε k m) : ℝ) / Fintype.card I =
      1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / Fintype.card I)) : k = 1 := by
  rcases mca_parameters D ε hr mca with one | ⟨rfl, sixteen⟩
  · exact one
  · have size : (Fintype.card I : ℝ) = 16 := by exact_mod_cast sixteen
    rw [size] at mca list
    norm_num [Real.sqrt_div] at mca list
    have first : cutoff (RankReview.mcaAnswer D ε 2) = 12 := by
      exact_mod_cast (show (cutoff (RankReview.mcaAnswer D ε 2) : ℝ) = 12 by linarith)
    have second : cutoff (RankReview.listAnswer D ε 2 m) = 12 := by
      exact_mod_cast (show (cutoff (RankReview.listAnswer D ε 2 m) : ℝ) = 12 by linarith)
    by_cases tiny : RankReview.budget F ε < Fintype.card F
    · have sep := SixteenJohnsonSeparation.separate_of_budget_lt D sixteen ε m tiny
      omega
    · rw [SixteenJohnsonSeparation.all_safe_of_field_budget D ε 2 (by omega)] at first
      simp [cutoff, sixteen] at first

/-- Equality for MCA can occur only in dimension one or at the sixteen-point
dimension-two code parameters. In the second case the list cutoff must differ. -/
theorem necessary {n k : ℕ} {withLists : Bool} (hr : hasPrizeRate n k)
    (existsCode : realizable n k withLists) :
    k = 1 ∨ k = 2 ∧ n = 16 ∧ withLists = false := by
  obtain ⟨F, I, _, _, _, _, _, D, ⟨sm⟩, card, _, mca, lists⟩ := existsCode
  subst n
  rcases mca_parameters D (prizeThreshold : ℝ≥0) hr mca with one | ⟨rfl, sixteen⟩
  · exact Or.inl one
  · refine Or.inr ⟨rfl, sixteen, ?_⟩
    cases withLists with
    | false => rfl
    | true =>
      have impossible := dimension_one_of_both D (prizeThreshold : ℝ≥0) hr 1 mca
        (lists rfl 1 (by decide))
      omega

/-- A single supplied code can have both operational cutoffs equal to Johnson
at every positive width exactly in dimension one. -/
theorem both_iff {n k : ℕ} (hr : hasPrizeRate n k) : realizable n k true ↔ k = 1 := by
  constructor
  · intro ex
    rcases necessary hr ex with one | ⟨_, _, h⟩
    · exact one
    · cases h
  · rintro rfl
    exact dimension_one hr true

end ProximityPrize.JointJohnsonEquality
