/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InvolutionClosedCount
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._E3StrataCount
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false

/-! Scratch: the count of negation-closed `2i`-subsets of a negation-closed `G ⊆ F`.
Direct port of `InvolutionClosedCount.isClosed_card_eq_choose` from `univ` to `G` (whose
elements are nonzero, so `-·` is fixed-point-free on `G`); the transversal is
`exists_neg_transversal`. This is the per-stratum subset multiplicity
`#{neg-closed S ⊆ G : |S| = 2i} = C(|G|/2, i)` feeding the E₃ assembly. -/

open Finset

namespace E3SubsetCount

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

open ArkLib.ProximityGap.Frontier.E3StrataCount (exists_neg_transversal)

/-- **`#{neg-closed S ⊆ G : |S| = 2i} = C(|G|/2, i)`.** For negation-closed `G` (`0 ∉ G`, char ≠ 2)
the bijection `U ↦ U ∪ (-U)` sends `i`-subsets of a negation transversal `T` to negation-closed
`2i`-subsets of `G`; inverse `S ↦ S ∩ T`. Port of `isClosed_card_eq_choose` over `G`. -/
theorem negClosed_subset_count (G : Finset F) (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G)
    (hneg : ∀ z ∈ G, -z ∈ G) (i : ℕ) :
    (G.powerset.filter (fun S => (∀ z ∈ S, -z ∈ S) ∧ S.card = 2 * i)).card
      = Nat.choose (G.card / 2) i := by
  classical
  obtain ⟨T, hsubT, hdisj, hcov, hTcard⟩ := exists_neg_transversal G h2 h0 hneg
  have hTc : T.card = G.card / 2 := by omega
  rw [← hTc, ← Finset.card_powersetCard i T]
  refine Finset.card_nbij' (fun S => S ∩ T) (fun U => U ∪ U.image (fun x => -x)) ?_ ?_ ?_ ?_
  · -- forward: S ↦ S ∩ T lands in powersetCard i T
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSG, hClosed, hcard⟩ := hS
    rw [Finset.mem_coe, Finset.mem_powersetCard]
    refine ⟨Finset.inter_subset_right, ?_⟩
    show (S ∩ T).card = i
    have hsplit : S = (S ∩ T) ∪ (S ∩ T).image (fun x => -x) := by
      apply Finset.Subset.antisymm
      · intro x hx
        have hmem : x ∈ T ∪ T.image (fun x => -x) := hcov ▸ hSG hx
        rw [Finset.mem_union] at hmem
        rcases hmem with hT | hiT
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
        · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
          exact Finset.mem_inter.mpr ⟨by have := hClosed (-y) hx; rwa [neg_neg] at this, hy⟩
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with h | h
        · exact (Finset.mem_inter.mp h).1
        · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
          exact hClosed y (Finset.mem_inter.mp hy).1
    have hdisj' : Disjoint (S ∩ T) ((S ∩ T).image (fun x => -x)) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_right
        (Finset.disjoint_of_subset_right (Finset.image_subset_image Finset.inter_subset_right) hdisj)
    have hc : S.card = 2 * (S ∩ T).card := by
      conv_lhs => rw [hsplit]
      rw [Finset.card_union_of_disjoint hdisj', Finset.card_image_of_injective _ neg_injective]; ring
    omega
  · -- backward: U ↦ U ∪ (-U) lands in the filter
    intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, hUcard⟩ := hU
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset]
    have hUG : U ⊆ G := hUT.trans hsubT
    have hd : Disjoint U (U.image (fun x => -x)) :=
      Finset.disjoint_of_subset_left hUT
        (Finset.disjoint_of_subset_right (Finset.image_subset_image hUT) hdisj)
    refine ⟨?_, ?_, ?_⟩
    · -- U ∪ (-U) ⊆ G
      intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact hUG h
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h; exact hneg y (hUG hy)
    · -- negation-closed
      intro z hz
      rw [Finset.mem_union] at hz ⊢
      rcases hz with h | h
      · right; exact Finset.mem_image_of_mem _ h
      · left; rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h; rwa [neg_neg]
    · -- card = 2 * i
      rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ neg_injective, hUcard]; ring
  · -- left inverse: (S ∩ T) ↦ recovers S
    intro S hS
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSG, hClosed, _⟩ := hS
    show (S ∩ T) ∪ (S ∩ T).image (fun x => -x) = S
    apply Finset.Subset.antisymm
    · intro x hx
      rw [Finset.mem_union] at hx
      rcases hx with h | h
      · exact (Finset.mem_inter.mp h).1
      · rw [Finset.mem_image] at h; obtain ⟨y, hy, rfl⟩ := h
        exact hClosed y (Finset.mem_inter.mp hy).1
    · intro x hx
      have hmem : x ∈ T ∪ T.image (fun x => -x) := hcov ▸ hSG hx
      rw [Finset.mem_union] at hmem
      rcases hmem with hT | hiT
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hT⟩)
      · rw [Finset.mem_image] at hiT; obtain ⟨y, hy, rfl⟩ := hiT
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, ?_, rfl⟩)
        exact Finset.mem_inter.mpr ⟨by have := hClosed (-y) hx; rwa [neg_neg] at this, hy⟩
  · -- right inverse: (U ∪ (-U)) ∩ T = U
    intro U hU
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hU
    obtain ⟨hUT, _⟩ := hU
    show (U ∪ U.image (fun x => -x)) ∩ T = U
    rw [Finset.union_inter_distrib_right]
    have h1 : U ∩ T = U := Finset.inter_eq_left.mpr hUT
    have h2 : U.image (fun x => -x) ∩ T = ∅ := by
      rw [← Finset.disjoint_iff_inter_eq_empty]
      exact Finset.disjoint_of_subset_left (Finset.image_subset_image hUT) hdisj.symm
    rw [h1, h2, Finset.union_empty]

end E3SubsetCount

#print axioms E3SubsetCount.negClosed_subset_count
