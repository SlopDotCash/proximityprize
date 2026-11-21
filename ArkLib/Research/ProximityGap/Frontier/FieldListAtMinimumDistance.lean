/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# A field-sized Reed–Solomon list at minimum distance

All scalar multiples of a minimum-weight nonzero word belong to the closed ball about zero.
-/

namespace ProximityGap.FieldListAtMinimumDistance

open Code LinearCode Finset

/-- At least one full field's worth of codewords lies in the ball at minimum distance. -/
theorem field_card_le_lambda {ι F : Type*} [Fintype ι] [Nonempty ι] [Fintype F] [Field F]
    [DecidableEq F] (C : Submodule F (ι → F)) (hd : 0 < Code.minDist (C : Set (ι → F))) :
    (Fintype.card F : ℕ∞) ≤ Code.Lambda (C : Set (ι → F))
      ((Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι) := by
  classical
  let W := {r : ℕ | ∃ c ∈ C, c ≠ 0 ∧ Code.wt c = r}
  have hdist : Code.minDist (C : Set (ι → F)) = sInf W := dist_eq_minWtCodewords
  have hne : W.Nonempty := by
    by_contra h
    rw [hdist, Set.not_nonempty_iff_eq_empty.mp h, Nat.sInf_empty] at hd
    omega
  obtain ⟨c, hc, hc0, hwt⟩ := Nat.sInf_mem hne
  have hw : Code.wt c = Code.minDist (C : Set (ι → F)) := hwt.trans hdist.symm
  let word := fun a : F ↦ a • c
  have hinj : Function.Injective word := smul_left_injective F hc0
  have hsub : (↑(univ.image word) : Set (ι → F)) ⊆
      closeCodewordsRel (C : Set (ι → F)) 0
        ((Code.minDist (C : Set (ι → F)) : ℝ) / Fintype.card ι) := by
    rw [← closeCodewords_eq_closeCodewordsRel]
    intro v hv
    obtain ⟨a, _, rfl⟩ := mem_image.mp hv
    refine ⟨C.smul_mem a hc, ?_⟩
    refine le_trans ?_ hw.le
    apply card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hzero
    exact hi (by simp [word, hzero])
  have hb := encard_le_Lambda_of_subset_closeCodewordsRel hsub
  rwa [Set.encard_coe_eq_coe_finsetCard, card_image_of_injective _ hinj, card_univ] at hb

#print axioms field_card_le_lambda

end ProximityGap.FieldListAtMinimumDistance
