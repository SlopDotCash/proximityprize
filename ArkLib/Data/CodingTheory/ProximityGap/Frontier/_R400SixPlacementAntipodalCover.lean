/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R393FourFiberPrimitiveDecomposition

/-!
# R400: quotient both internal orientations of an antipodal insertion

R393 quotients the order of the two residual coordinates and obtains twelve permutation cells.
When `G` is closed under negation, swapping the two antipodal coordinates is also redundant: it is
absorbed by replacing the inserted element `x` with `-x`. This file proves that the resulting
six-cell presentation equals R393's full cover and obtains
`rep₄(c) ≤ primitive₄(c) + 6 |G| rep₂(c)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover

open ArkLib.ProximityGap.Frontier.R390CharZeroNonzeroRepFourBound
open ArkLib.ProximityGap.Frontier.R392PairFiberNecessaryForFourFiber
open ArkLib.ProximityGap.Frontier.R393FourFiberPrimitiveDecomposition

variable {F : Type*} [Field F] [DecidableEq F]

/-- Swap the two antipodal slots of an inserted tuple. -/
def swapAntipodal : Equiv.Perm (Fin 4) := Equiv.swap 0 1

/-- One representative for each choice of the two antipodal coordinate positions. -/
def canonicalPermsSix : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter (fun σ => σ.symm 0 < σ.symm 1 ∧ σ.symm 2 < σ.symm 3)

/-- The six-placement antipodal cover. -/
noncomputable def antipodalCoverSix (G : Finset F) (c : F) : Finset (Fin 4 → F) :=
  canonicalPermsSix.biUnion fun σ =>
    (G ×ˢ pairFiber G c).image (permutedInsert σ)

@[simp] theorem card_canonicalPermsSix : canonicalPermsSix.card = 6 := by decide

/-- Swapping antipodal slots is absorbed by negating the inserted element. -/
theorem permutedInsert_swapAntipodal (σ : Equiv.Perm (Fin 4)) (x : F) (u : Fin 2 → F) :
    permutedInsert (σ.trans swapAntipodal) (-x, u) = permutedInsert σ (x, u) := by
  funext i
  unfold permutedInsert
  change insertAntipodal (-x) u (swapAntipodal (σ i)) = insertAntipodal x u (σ i)
  have h0 : swapAntipodal (0 : Fin 4) = 1 := by decide
  have h1 : swapAntipodal (1 : Fin 4) = 0 := by decide
  have h2 : swapAntipodal (2 : Fin 4) = 2 := by decide
  have h3 : swapAntipodal (3 : Fin 4) = 3 := by decide
  generalize hj : σ i = j
  fin_cases j <;> simp [h0, h1, h2, h3, insertAntipodal]

/-- Every coordinate permutation normalizes into the six representatives after independently
swapping the residual and antipodal slots. This is a finite statement about `S₄`. -/
theorem mem_six_normalization_cases (σ : Equiv.Perm (Fin 4)) :
    σ ∈ canonicalPermsSix ∨
      σ.trans swapResidual ∈ canonicalPermsSix ∨
      σ.trans swapAntipodal ∈ canonicalPermsSix ∨
      (σ.trans swapResidual).trans swapAntipodal ∈ canonicalPermsSix := by
  revert σ
  decide

/-- The six-cell presentation is contained in the original antipodal cover. -/
theorem antipodalCoverSix_subset (G : Finset F) (c : F) :
    antipodalCoverSix G c ⊆ antipodalCover G c := by
  classical
  intro a ha
  rw [antipodalCoverSix, Finset.mem_biUnion] at ha
  obtain ⟨σ, _, haσ⟩ := ha
  rw [antipodalCover, Finset.mem_biUnion]
  exact ⟨σ, Finset.mem_univ _, haσ⟩

/-- Negation closure makes the original 24-permutation cover equal to the six-placement cover. -/
theorem antipodalCover_eq_six
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    antipodalCover G c = antipodalCoverSix G c := by
  classical
  apply Finset.Subset.antisymm
  · intro a ha
    rw [antipodalCover, Finset.mem_biUnion] at ha
    obtain ⟨σ, _, haσ⟩ := ha
    rw [Finset.mem_image] at haσ
    obtain ⟨⟨x, u⟩, hxu, rfl⟩ := haσ
    rw [Finset.mem_product] at hxu
    rcases mem_six_normalization_cases σ with hσ | hσ | hσ | hσ
    · rw [antipodalCoverSix, Finset.mem_biUnion]
      exact ⟨σ, hσ, Finset.mem_image_of_mem _ (Finset.mem_product.mpr hxu)⟩
    · rw [antipodalCoverSix, Finset.mem_biUnion]
      refine ⟨σ.trans swapResidual, hσ, ?_⟩
      have hu := swapPair_mem_pairFiber hxu.2
      rw [Finset.mem_image]
      exact ⟨(x, swapPair u), Finset.mem_product.mpr ⟨hxu.1, hu⟩,
        permutedInsert_swapResidual σ x u⟩
    · rw [antipodalCoverSix, Finset.mem_biUnion]
      refine ⟨σ.trans swapAntipodal, hσ, ?_⟩
      rw [Finset.mem_image]
      exact ⟨(-x, u), Finset.mem_product.mpr ⟨hneg x hxu.1, hxu.2⟩,
        permutedInsert_swapAntipodal σ x u⟩
    · rw [antipodalCoverSix, Finset.mem_biUnion]
      refine ⟨(σ.trans swapResidual).trans swapAntipodal, hσ, ?_⟩
      rw [Finset.mem_image]
      refine ⟨(-x, swapPair u),
        Finset.mem_product.mpr ⟨hneg x hxu.1, swapPair_mem_pairFiber hxu.2⟩, ?_⟩
      rw [permutedInsert_swapAntipodal, permutedInsert_swapResidual]
  · exact antipodalCoverSix_subset G c

/-- The six-placement cover has the expected overlap-blind cardinality bound. -/
theorem card_antipodalCoverSix_le (G : Finset F) (c : F) :
    (antipodalCoverSix G c).card ≤ 6 * (G.card * (pairFiber G c).card) := by
  classical
  calc
    (antipodalCoverSix G c).card ≤
        ∑ σ ∈ canonicalPermsSix,
          ((G ×ˢ pairFiber G c).image (permutedInsert σ)).card := by
            unfold antipodalCoverSix
            exact Finset.card_biUnion_le
    _ ≤ ∑ _σ ∈ canonicalPermsSix, (G ×ˢ pairFiber G c).card := by
          apply Finset.sum_le_sum
          intro σ _
          exact Finset.card_image_le
    _ = 6 * (G.card * (pairFiber G c).card) := by
          simp [Finset.card_product, card_canonicalPermsSix]

/-- **Six-placement antipodal-cover bound.** -/
theorem card_antipodalCover_le_six
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    (antipodalCover G c).card ≤ 6 * (G.card * (pairFiber G c).card) := by
  rw [antipodalCover_eq_six G hneg c]
  exact card_antipodalCoverSix_le G c

/-- The primitive remainder and antipodal cover are an exact disjoint partition of the four-fiber.
R393 only needed a cover inequality; negation closure upgrades it to cardinal equality. -/
theorem card_fourFiber_eq_primitive_add_cover
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    (fourFiber G c).card =
      (primitiveFourFiber G c).card + (antipodalCover G c).card := by
  have hsub := antipodalCover_subset_fourFiber G hneg c
  rw [primitiveFourFiber, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsub]
  have hcard := Finset.card_le_card hsub
  omega

/-- Prize-facing primitive/antipodal decomposition with all internal insertion symmetries
quotiented out. -/
theorem card_fourFiber_le_primitive_add_pair_six
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) :
    (fourFiber G c).card ≤
      (primitiveFourFiber G c).card + 6 * (G.card * (pairFiber G c).card) := by
  rw [card_fourFiber_eq_primitive_add_cover G hneg c]
  exact Nat.add_le_add_left (card_antipodalCover_le_six G hneg c) _

/-- Consumer form: a primitive linear bound and any pointwise pair bound combine with coefficient
six, rather than R393's original coefficient twenty-four. -/
theorem card_fourFiber_le_of_components_six
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G) (c : F) (A B : ℕ)
    (hprimitive : (primitiveFourFiber G c).card ≤ A * G.card)
    (hpair : (pairFiber G c).card ≤ B) :
    (fourFiber G c).card ≤ (A + 6 * B) * G.card := by
  have hsplit := card_fourFiber_le_primitive_add_pair_six G hneg c
  have hpairMul : G.card * (pairFiber G c).card ≤ G.card * B :=
    Nat.mul_le_mul_left G.card hpair
  calc
    (fourFiber G c).card
        ≤ (primitiveFourFiber G c).card + 6 * (G.card * (pairFiber G c).card) := hsplit
    _ ≤ A * G.card + 6 * (G.card * B) :=
          Nat.add_le_add hprimitive (Nat.mul_le_mul_left 6 hpairMul)
    _ = (A + 6 * B) * G.card := by ring

/-- The arithmetic pair-fiber residual suggested by the first quartic-threshold counterexample. -/
def PairMultiplicityNine (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairFiber G c).card ≤ 9

/-- The complementary primitive-fiber residual under the six-placement decomposition. -/
def PrimitiveFourBoundFiftyOne (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (primitiveFourFiber G c).card ≤ 51 * G.card

/-- **Exact `105|G|` capstone for the sharpened finite-characteristic route.** -/
theorem card_fourFiber_le_105_mul_card_of_nine
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G)
    (hpair : PairMultiplicityNine G) (hprimitive : PrimitiveFourBoundFiftyOne G)
    {c : F} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card := by
  have h := card_fourFiber_le_of_components_six G hneg c 51 9
    (hprimitive c hc) (hpair c hc)
  norm_num at h ⊢
  exact h

/-- Parity-stable version of the pair-fiber residual. Unlike a bound by nine, this does not force
every off-diagonal (hence even-sized) fiber down to eight. -/
def PairMultiplicityTen (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (pairFiber G c).card ≤ 10

/-- Complementary primitive budget for the parity-stable split `45 + 6*10 = 105`. -/
def PrimitiveFourBoundFortyFive (G : Finset F) : Prop :=
  ∀ c : F, c ≠ 0 → (primitiveFourFiber G c).card ≤ 45 * G.card

/-- **Preferred parity-stable `105|G|` capstone.** -/
theorem card_fourFiber_le_105_mul_card_of_ten
    (G : Finset F) (hneg : ∀ x ∈ G, -x ∈ G)
    (hpair : PairMultiplicityTen G) (hprimitive : PrimitiveFourBoundFortyFive G)
    {c : F} (hc : c ≠ 0) :
    (fourFiber G c).card ≤ 105 * G.card := by
  have h := card_fourFiber_le_of_components_six G hneg c 45 10
    (hprimitive c hc) (hpair c hc)
  norm_num at h ⊢
  exact h

end ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_antipodalCoverSix_le
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_fourFiber_le_primitive_add_pair_six
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_fourFiber_eq_primitive_add_cover
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_fourFiber_le_of_components_six
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_fourFiber_le_105_mul_card_of_nine
#print axioms
  ArkLib.ProximityGap.Frontier.R400SixPlacementAntipodalCover.card_fourFiber_le_105_mul_card_of_ten
