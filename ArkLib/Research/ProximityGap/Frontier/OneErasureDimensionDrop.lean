/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCANearCapacityGeneralRate
import ArkLib.Research.ProximityGap.Frontier.CircuitDensity
import ArkLib.Research.ProximityGap.MCAEndpointLower

/-! # Exact MCA error in the two dimensions at the one-erasure boundary -/

open Finset
open scoped NNReal ENNReal
namespace ProximityGap.OneErasureDimensionDrop

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The codimension-one code has worst-case probability exactly one over the
field size at every radius. The whole domain is its only minimal interpolation circuit. -/
theorem codimension_one {n k : ℕ} [NeZero n] (dom : Fin n ↪ F) (h : k+1=n) (δ : ℝ≥0) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ = 1/(Fintype.card F : ℝ≥0∞) := by
  apply le_antisymm
  · rw [← Nat.cast_one (R := ℝ≥0∞)]
    apply epsMCA_le_of_badCount_le (F := F) _ δ 1
    intro u
    simpa [h] using CircuitDensity.mca_count_le_choose dom k δ (u 0) (u 1)
  · simpa only [one_div] using epsMCA_ge_inv_card dom k δ (by simpa [Nat.add_comm] using h.le)

/-- At codimension two every one-site omission contributes its own bad label at one
erasure. The circuit bound certifies that no other pair has more. -/
theorem codimension_two {n k : ℕ} [NeZero n] (dom : Fin n ↪ F) (hk : 1≤k) (h : k+2=n)
    (δ : ℝ≥0) (hδ : 1-((k+1 : ℕ) : ℝ≥0)/(n : ℝ≥0) ≤ δ) :
    epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ =
      (n : ℝ≥0∞)/(Fintype.card F : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · apply epsMCA_le_of_badCount_le (F := F) _ δ n
    intro u
    simpa only [Fintype.card_fin, ← h, Nat.choose_succ_self_right] using
      CircuitDensity.mca_count_le_choose dom k δ (u 0) (u 1)
  · let W (i : Fin n) := (univ : Finset (Fin n)).erase i
    have sum_inj : Function.Injective (fun i => -(∑ j ∈ W i, dom j)) := by
      intro i j he
      have he' : (∑ x ∈ W i, dom x) = ∑ x ∈ W j, dom x := neg_inj.mp he
      apply dom.injective
      have hi := Finset.add_sum_erase univ dom (mem_univ i)
      have hj := Finset.add_sum_erase univ dom (mem_univ j)
      change dom i + (∑ x ∈ W i, dom x) = _ at hi
      rw [he'] at hi
      exact add_right_cancel (hi.trans hj.symm)
    have winj : Function.Injective W := fun i j he => sum_inj (congrArg (fun S => -(∑ x ∈ S, dom x)) he)
    have cap := MCANearCapacityGK.epsMCA_ge_of_window_family dom k hk (univ.image W) (by
      intro S hS
      obtain ⟨i,_,rfl⟩ := mem_image.mp hS
      simp [W, ← h]) (by
      rintro S hS T hT he
      obtain ⟨i,_,rfl⟩ := mem_image.mp hS
      obtain ⟨j,_,rfl⟩ := mem_image.mp hT
      exact congrArg W (sum_inj he))
    rw [Finset.card_image_of_injective _ winj, card_univ, Fintype.card_fin] at cap
    exact cap.trans (epsMCA_mono _ hδ)

/-- At one erasure increasing the dimension from n−2 to n−1 strictly decreases the
worst-case line-MCA error. Both values are exact on every injective domain. -/
theorem strict_drop {n k : ℕ} [NeZero n] (dom : Fin n ↪ F) (hk : 1≤k) (h : k+2=n)
    (δ : ℝ≥0) (hδ : 1-((k+1 : ℕ) : ℝ≥0)/(n : ℝ≥0) ≤ δ) :
    epsMCA (F := F) (ReedSolomon.code dom (k+1) : Set (Fin n → F)) δ <
      epsMCA (F := F) (ReedSolomon.code dom k : Set (Fin n → F)) δ := by
  rw [codimension_one dom h, codimension_two dom hk h δ hδ]
  have hq : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (ENNReal.div_lt_div_iff_left hq (by simp)).mpr (by exact_mod_cast (show 1<n by omega))

#print axioms codimension_one
#print axioms codimension_two
#print axioms strict_drop
end ProximityGap.OneErasureDimensionDrop
