/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R392PairFiberNecessaryForFourFiber

/-!
# R393: split a four-fiber into antipodal insertions and a primitive remainder

Take all coordinate permutations of tuples `(x,-x,u,v)` with `x ∈ G` and `u+v=c`. Their union is
the antipodal cover.  Its cardinality is at most `24|G| rep₂(c)`.  Removing it from the four-fiber
defines the primitive remainder, and gives the exact prize-facing reduction

`rep₄(c) ≤ primitive₄(c) + 24|G| rep₂(c)`.

The constant `24` is deliberately overlap-blind. R397 later refuted the proposed pointwise
pair-multiplicity-four cap beyond the quartic threshold, so sharpening this cover is not merely
cosmetic if one wants the char-zero constant `105`; it is a live alternative to a stronger
primitive-remainder estimate.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition

open ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound
open ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber

variable {F : Type*} [Field F] [DecidableEq F]

/-- Permute the coordinates of an antipodal insertion. -/
def permutedInsert (σ : Equiv.Perm (Fin 4)) (xu : F × (Fin 2 → F)) : Fin 4 → F :=
  fun i => insertAntipodal xu.1 xu.2 (σ i)

/-- Swap the two residual coordinates of an inserted four-tuple. -/
def swapResidual : Equiv.Perm (Fin 4) := Equiv.swap 2 3

/-- Swap an ordered residual pair. -/
def swapPair (u : Fin 2 → F) : Fin 2 → F := fun i => u (Equiv.swap 0 1 i)

/-- One representative from each pair of permutations differing by a residual-coordinate swap. -/
def canonicalPerms : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter (fun σ => σ.symm 2 < σ.symm 3)

/-- The canonical twelve-permutation antipodal cover. -/
noncomputable def antipodalCoverTwelve (G : Finset F) (c : F) : Finset (Fin 4 → F) :=
  canonicalPerms.biUnion fun σ =>
    (G ×ˢ pairFiber G c).image (permutedInsert σ)

/-- Union of all coordinate permutations of inserted-antipodal tuples. -/
noncomputable def antipodalCover (G : Finset F) (c : F) : Finset (Fin 4 → F) :=
  Finset.univ.biUnion fun σ : Equiv.Perm (Fin 4) =>
    (G ×ˢ pairFiber G c).image (permutedInsert σ)

@[simp] theorem card_canonicalPerms : canonicalPerms.card = 12 := by decide

/-- Swapping the residual pair keeps it in the same two-fiber. -/
theorem swapPair_mem_pairFiber {G : Finset F} {c : F} {u : Fin 2 → F}
    (hu : u ∈ pairFiber G c) : swapPair u ∈ pairFiber G c := by
  rw [pairFiber, Finset.mem_filter] at hu ⊢
  refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [swapPair] using (Fintype.mem_piFinset.mp hu.1 1)
    · simpa [swapPair] using (Fintype.mem_piFinset.mp hu.1 0)
  · simpa [swapPair, add_comm] using hu.2

/-- Swapping the residual slots and the residual ordered pair leaves the inserted tuple unchanged. -/
theorem permutedInsert_swapResidual (σ : Equiv.Perm (Fin 4)) (x : F) (u : Fin 2 → F) :
    permutedInsert (σ.trans swapResidual) (x, swapPair u) = permutedInsert σ (x, u) := by
  funext i
  unfold permutedInsert
  change insertAntipodal x (swapPair u) (swapResidual (σ i)) = insertAntipodal x u (σ i)
  have h0 : swapResidual (0 : Fin 4) = 0 := by decide
  have h1 : swapResidual (1 : Fin 4) = 1 := by decide
  have h2 : swapResidual (2 : Fin 4) = 3 := by decide
  have h3 : swapResidual (3 : Fin 4) = 2 := by decide
  generalize hj : σ i = j
  fin_cases j <;> simp [h0, h1, h2, h3, swapPair, insertAntipodal]

/-- Every permutation has a canonical representative after possibly swapping residual slots. -/
theorem mem_canonical_or_swapped (σ : Equiv.Perm (Fin 4)) :
    σ ∈ canonicalPerms ∨ σ.trans swapResidual ∈ canonicalPerms := by
  simp only [canonicalPerms, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : σ.symm 2 ≠ σ.symm 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (σ.symm.injective h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl h
  · right
    simpa [swapResidual] using h

/-- The 24-permutation presentation and the canonical 12-permutation presentation define the
same antipodal cover. -/
theorem antipodalCover_eq_twelve (G : Finset F) (c : F) :
    antipodalCover G c = antipodalCoverTwelve G c := by
  classical
  apply Finset.Subset.antisymm
  · intro a ha
    rw [antipodalCover, Finset.mem_biUnion] at ha
    obtain ⟨σ, _, haσ⟩ := ha
    rw [Finset.mem_image] at haσ
    obtain ⟨⟨x, u⟩, hxu, rfl⟩ := haσ
    rcases mem_canonical_or_swapped σ with hσ | hσ
    · rw [antipodalCoverTwelve, Finset.mem_biUnion]
      exact ⟨σ, hσ, Finset.mem_image_of_mem _ hxu⟩
    · rw [antipodalCoverTwelve, Finset.mem_biUnion]
      refine ⟨σ.trans swapResidual, hσ, ?_⟩
      rw [Finset.mem_product] at hxu
      have hswap : (x, swapPair u) ∈ G ×ˢ pairFiber G c :=
        Finset.mem_product.mpr ⟨hxu.1, swapPair_mem_pairFiber hxu.2⟩
      rw [Finset.mem_image]
      exact ⟨(x, swapPair u), hswap, permutedInsert_swapResidual σ x u⟩
  · intro a ha
    rw [antipodalCoverTwelve, Finset.mem_biUnion] at ha
    obtain ⟨σ, _, haσ⟩ := ha
    rw [antipodalCover, Finset.mem_biUnion]
    exact ⟨σ, Finset.mem_univ _, haσ⟩

/-- Four-fiber tuples not generated by any antipodal insertion. -/
noncomputable def primitiveFourFiber (G : Finset F) (c : F) : Finset (Fin 4 → F) :=
  fourFiber G c \ antipodalCover G c

/-- Permuting an inserted tuple preserves membership in the four-fiber. -/
theorem permutedInsert_in_fourFiber
    {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) {c : F}
    (σ : Equiv.Perm (Fin 4)) {xu : F × (Fin 2 → F)}
    (hxu : xu ∈ G ×ˢ pairFiber G c) :
    permutedInsert σ xu ∈ fourFiber G c := by
  rw [Finset.mem_product] at hxu
  have hbase := insertAntipodal_in_fourFiber hneg hxu.1 hxu.2
  rw [fourFiber, Finset.mem_filter] at hbase ⊢
  refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
  · intro i
    exact (Fintype.mem_piFinset.mp hbase.1) (σ i)
  · exact (Equiv.sum_comp σ (insertAntipodal xu.1 xu.2)).trans hbase.2

/-- The entire antipodal cover lies in the target four-fiber. -/
theorem antipodalCover_subset_fourFiber
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    antipodalCover G c ⊆ fourFiber G c := by
  classical
  intro a ha
  rw [antipodalCover, Finset.mem_biUnion] at ha
  obtain ⟨σ, _, haσ⟩ := ha
  rw [Finset.mem_image] at haσ
  obtain ⟨xu, hxu, rfl⟩ := haσ
  exact permutedInsert_in_fourFiber hneg σ hxu

/-- The overlap-blind 24-permutation bound for the antipodal cover. -/
theorem card_antipodalCover_le
    (G : Finset F) (c : F) :
    (antipodalCover G c).card ≤ 24 * (G.card * (pairFiber G c).card) := by
  classical
  calc
    (antipodalCover G c).card
        ≤ ∑ σ : Equiv.Perm (Fin 4),
            ((G ×ˢ pairFiber G c).image (permutedInsert σ)).card := by
          unfold antipodalCover
          exact Finset.card_biUnion_le
    _ ≤ ∑ _σ : Equiv.Perm (Fin 4), (G ×ˢ pairFiber G c).card := by
          apply Finset.sum_le_sum
          intro σ _
          exact Finset.card_image_le
    _ = 24 * (G.card * (pairFiber G c).card) := by
          rw [Finset.card_product]
          norm_num [Fintype.card_perm]

/-- **Sharpened antipodal-cover bound.** Canonicalizing the order of the two residual coordinate
positions removes the systematic factor-two duplication in the 24-permutation presentation. -/
theorem card_antipodalCover_le_twelve
    (G : Finset F) (c : F) :
    (antipodalCover G c).card ≤ 12 * (G.card * (pairFiber G c).card) := by
  classical
  rw [antipodalCover_eq_twelve]
  calc
    (antipodalCoverTwelve G c).card
        ≤ ∑ σ ∈ canonicalPerms,
            ((G ×ˢ pairFiber G c).image (permutedInsert σ)).card := by
          unfold antipodalCoverTwelve
          exact Finset.card_biUnion_le
    _ ≤ ∑ _σ ∈ canonicalPerms, (G ×ˢ pairFiber G c).card := by
          apply Finset.sum_le_sum
          intro σ _
          exact Finset.card_image_le
    _ = 12 * (G.card * (pairFiber G c).card) := by
          simp [Finset.card_product, card_canonicalPerms]

/-- The four-fiber is covered by its primitive remainder and the antipodal cover. -/
theorem fourFiber_subset_primitive_union_cover (G : Finset F) (c : F) :
    fourFiber G c ⊆ primitiveFourFiber G c ∪ antipodalCover G c := by
  intro a ha
  by_cases hd : a ∈ antipodalCover G c
  · exact Finset.mem_union_right _ hd
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hd⟩)

/-- **Primitive/antipodal decomposition bound.** -/
theorem card_fourFiber_le_primitive_add_pair
    (G : Finset F) (c : F) :
    (fourFiber G c).card ≤
      (primitiveFourFiber G c).card + 24 * (G.card * (pairFiber G c).card) := by
  calc
    (fourFiber G c).card
        ≤ (primitiveFourFiber G c ∪ antipodalCover G c).card :=
          Finset.card_le_card (fourFiber_subset_primitive_union_cover G c)
    _ ≤ (primitiveFourFiber G c).card + (antipodalCover G c).card :=
          Finset.card_union_le _ _
    _ ≤ (primitiveFourFiber G c).card + 24 * (G.card * (pairFiber G c).card) :=
          Nat.add_le_add_left (card_antipodalCover_le G c) _

/-- Sharpened primitive/antipodal decomposition using the canonical twelve-permutation cover. -/
theorem card_fourFiber_le_primitive_add_pair_twelve
    (G : Finset F) (c : F) :
    (fourFiber G c).card ≤
      (primitiveFourFiber G c).card + 12 * (G.card * (pairFiber G c).card) := by
  calc
    (fourFiber G c).card
        ≤ (primitiveFourFiber G c ∪ antipodalCover G c).card :=
          Finset.card_le_card (fourFiber_subset_primitive_union_cover G c)
    _ ≤ (primitiveFourFiber G c).card + (antipodalCover G c).card :=
          Finset.card_union_le _ _
    _ ≤ (primitiveFourFiber G c).card + 12 * (G.card * (pairFiber G c).card) :=
          Nat.add_le_add_left (card_antipodalCover_le_twelve G c) _

/-- Consumer form: constant pair multiplicity plus a linear primitive bound gives a linear
four-fiber bound. -/
theorem card_fourFiber_le_of_components
    (G : Finset F) (c : F) (A B : ℕ)
    (hprimitive : (primitiveFourFiber G c).card ≤ A * G.card)
    (hpair : (pairFiber G c).card ≤ B) :
    (fourFiber G c).card ≤ (A + 24 * B) * G.card := by
  have hsplit := card_fourFiber_le_primitive_add_pair G c
  have hpairMul : G.card * (pairFiber G c).card ≤ G.card * B :=
    Nat.mul_le_mul_left G.card hpair
  have hpair24 : 24 * (G.card * (pairFiber G c).card) ≤ 24 * (G.card * B) :=
    Nat.mul_le_mul_left 24 hpairMul
  calc
    (fourFiber G c).card
        ≤ (primitiveFourFiber G c).card + 24 * (G.card * (pairFiber G c).card) := hsplit
    _ ≤ A * G.card + 24 * (G.card * B) := Nat.add_le_add hprimitive hpair24
    _ = (A + 24 * B) * G.card := by ring

end ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition.card_antipodalCover_le
#print axioms
  ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition.card_fourFiber_le_of_components
#print axioms
  ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition.card_antipodalCover_le_twelve
