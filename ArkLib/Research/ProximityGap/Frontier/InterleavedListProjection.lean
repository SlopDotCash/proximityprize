/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.CodingTheory.InterleavedCode.Projection
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# Scalar and interleaved list budgets over a large field

For a linear code over a finite field, a linear combination of rows preserves every
coordinate of agreement. A finite list of interleaved words has a separating row
combination whenever its number of unordered pairs is at most the field cardinality.
At the 128-bit prize budget, this gives the same closed-ball test at every arity.
-/

open Code
open scoped BigOperators

namespace ProximityGap.InterleavedListProjection

variable {F ι κ : Type*} [Field F] [Fintype F] [Fintype ι] [Fintype κ]

private noncomputable def project (w : ι → κ → F) : (κ → F) →ₗ[F] (ι → F) :=
  Fintype.linearCombination F (fun j i ↦ w i j)

private def constantOn (s : Finset (ι → κ → F)) : Submodule F (κ → F) where
  carrier := {l | ∀ x ∈ s, ∀ y ∈ s, project x l = project y l}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx y hy
    rw [map_add, map_add, ha x hx y hy, hb x hx y hy]
  smul_mem' := by
    intro a b hb x hx y hy
    rw [map_smul, map_smul, hb x hx y hy]

/-- A finite list can be separated by a single linear combination of its rows whenever
there are at most as many pairs as field elements. -/
theorem exists_separating_projection (s : Finset (ι → κ → F))
    (hs : s.card.choose 2 ≤ Nat.card F) :
    ∃ l : κ → F, Set.InjOn (fun w ↦ ∑ j, l j • (fun i ↦ w i j)) (↑s : Set (ι → κ → F)) := by
  classical
  have hproper : ∀ t ∈ s.powersetCard 2, constantOn t ≠ ⊤ := by
    intro t ht htop
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ht).2
    apply hxy
    funext i j
    have hj : Pi.single j (1 : F) ∈ constantOn ({x,y} : Finset _) := htop ▸ Submodule.mem_top
    have heq := hj x (by simp) y (by simp)
    simpa [project] using congrFun heq i
  obtain ⟨l, hl⟩ := Submodule.exists_forall_notMem_of_card_le
    (s.powersetCard 2) constantOn hproper (by simpa using hs)
  refine ⟨l, ?_⟩
  intro x hx y hy heq
  by_contra hxy
  apply hl {x,y} (Finset.mem_powersetCard.mpr ⟨by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hy'
    · exact hx
    · exact Finset.mem_singleton.mp hy' ▸ hy, by simp [hxy]⟩)
  intro a ha b hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact heq
  · exact heq.symm
  · rfl

/-- At a budget with at most `q` forbidden pairs, a scalar list bound transfers at the
same radius to every interleaving of a linear code. -/
theorem interleaved_le_of_scalar_le [Nonempty ι] (C : Submodule F (ι → F)) (δ : ℝ) (B : ℕ)
    (hB : (B + 1).choose 2 ≤ Nat.card F) (h : Lambda (C : Set (ι → F)) δ ≤ B) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B := by
  classical
  apply Lambda_le_of_forall_finset_card_le
  intro f T hT
  by_contra! htoo
  obtain ⟨s, hsT, hcard⟩ := Finset.exists_subset_card_eq (show B+1 ≤ T.card by omega)
  obtain ⟨l, hsep⟩ := exists_separating_projection s (hcard ▸ hB)
  let P (v : ι → κ → F) : ι → F := ∑ j, l j • (fun i ↦ v i j)
  have hclose : (↑(s.image P) : Set (ι → F)) ⊆ closeCodewordsRel (C : Set (ι → F)) (P f) δ := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hc, hd⟩ := mem_closeCodewordsRel_iff.mp (hT w (hsT hw))
    apply mem_closeCodewordsRel_iff.mpr
    refine ⟨C.sum_mem fun j _ ↦ C.smul_mem (l j) (hc j), ?_⟩
    have hdist : relHammingDist (P f) (P w) ≤ relHammingDist f w := by
      unfold relHammingDist
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hd' := hammingDist_comp_le_hammingDist (fun (_ : ι) (z : κ → F) ↦ ∑ j, l j * z j)
        (x := f) (y := w)
      have hP (v : ι → κ → F) : P v = fun i ↦ ∑ j, l j * v i j := by
        funext i
        simp [P, Finset.sum_apply]
      have hn : hammingDist (P f) (P w) ≤ hammingDist f w := by
        simpa only [hP] using hd'
      exact_mod_cast hn
    exact (show (relHammingDist (P f) (P w) : ℝ) ≤ relHammingDist f w by exact_mod_cast hdist).trans hd
  have hsize := (encard_le_Lambda_of_subset_closeCodewordsRel hclose).trans h
  have himage : (s.image P).card = s.card := Finset.card_image_of_injOn hsep
  simp only [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at hsize
  omega

/-- A nonempty interleaving and its base code cross a small integer list budget
at precisely the same radii. -/
theorem list_budget_iff [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F)) (δ : ℝ)
    (B : ℕ) (hB : (B + 1).choose 2 ≤ Nat.card F) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ B ↔
      Lambda (C : Set (ι → F)) δ ≤ B := by
  classical
  refine ⟨fun h ↦ ?_, interleaved_le_of_scalar_le C δ B hB⟩
  apply Lambda_le_iff_forall_encard_le.mpr
  intro f
  let e : F → (κ → F) := fun v _ ↦ v
  have hinj : Function.Injective e := fun _ _ heq ↦ congrFun heq (Classical.arbitrary κ)
  let S := closeCodewordsRel (C : Set (ι → F)) f δ
  have hmaps : (fun c ↦ e ∘ c) '' S ⊆
      closeCodewordsRel (interleavedCodeSet (κ := κ) (C : Set (ι → F))) (e ∘ f) δ := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hC, hd⟩ := mem_closeCodewordsRel_iff.mp hc
    apply mem_closeCodewordsRel_iff.mpr
    exact ⟨fun _ ↦ hC, by rw [relHammingDist_comp hinj]; exact hd⟩
  have hword : Set.InjOn (fun c : ι → F ↦ e ∘ c) S :=
    fun _ _ _ _ heq ↦ funext fun i ↦ hinj (congrFun heq i)
  exact hword.encard_image ▸ (encard_le_Lambda_of_subset_closeCodewordsRel hmaps).trans h

/-- The list budget for 128 bits of security satisfies the pair hypothesis on
every field in the sub-256-bit prize envelope. -/
theorem prize_list_budget_iff [Nonempty ι] [Nonempty κ] (C : Submodule F (ι → F)) (δ : ℝ)
    (hq : Nat.card F < 2 ^ 256) :
    Lambda (interleavedCodeSet (κ := κ) (C : Set (ι → F))) δ ≤ (Nat.card F / 2 ^ 128 : ℕ) ↔
      Lambda (C : Set (ι → F)) δ ≤ (Nat.card F / 2 ^ 128 : ℕ) := by
  apply list_budget_iff
  let q := Nat.card F
  let B := q / 2 ^ 128
  have hB : B < 2 ^ 128 := by
    apply (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2 ^ 128)).mpr
    norm_num [q] at hq ⊢
    exact hq
  have hround : 2 ^ 128 * B ≤ q := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_le_self q (2 ^ 128)
  have hside : B + 1 ≤ 2 ^ 128 := hB
  have hmul : (B + 1) * B ≤ q := (Nat.mul_le_mul_right B hside).trans hround
  change (B + 1).choose 2 ≤ q
  rw [Nat.choose_two_right]
  exact (Nat.div_le_self _ 2).trans (by simpa using hmul)

end ProximityGap.InterleavedListProjection

#print axioms ProximityGap.InterleavedListProjection.exists_separating_projection
#print axioms ProximityGap.InterleavedListProjection.list_budget_iff
#print axioms ProximityGap.InterleavedListProjection.prize_list_budget_iff
