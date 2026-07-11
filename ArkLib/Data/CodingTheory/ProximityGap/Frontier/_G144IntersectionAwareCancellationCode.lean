/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G143DepthStratifiedSubsetAccidents

/-!
# G144: the intersection-aware cancellation code

G143 identifies why the naive lower-depth map is not injective: cancelling an equal-sum pair
forgets its common intersection.  This file restores exactly that information.  The code

`(S,T) ↦ (S \ T, T \ S, S ∩ T)`

is injective, its three components are pairwise disjoint, and on the depth-`t` stratum their
cardinalities are `t,t,r-t`.  The two core sums agree.  Hence all lower-depth multiplicity is now
localized to the choice of the common `(r-t)`-subset outside the two cores.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G144IntersectionAwareCancellationCode

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G142SubsetCollisionCancellationCore
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- The information-preserving cancellation code: left core, right core, common intersection. -/
def cancellationCode (p : Finset F × Finset F) :
    (Finset F × Finset F) × Finset F :=
  ((p.1 \ p.2, p.2 \ p.1), p.1 ∩ p.2)

theorem left_reconstruct_set (S T : Finset F) :
    (S \ T) ∪ (S ∩ T) = S := by
  ext x
  simp
  tauto

theorem right_reconstruct_set (S T : Finset F) :
    (T \ S) ∪ (S ∩ T) = T := by
  ext x
  simp
  tauto

/-- Restoring the common intersection makes cancellation injective. -/
theorem cancellationCode_injective :
    Function.Injective (cancellationCode : Finset F × Finset F →
      (Finset F × Finset F) × Finset F) := by
  intro p q h
  have hL : p.1 \ p.2 = q.1 \ q.2 := congrArg (fun z => z.1.1) h
  have hR : p.2 \ p.1 = q.2 \ q.1 := congrArg (fun z => z.1.2) h
  have hI : p.1 ∩ p.2 = q.1 ∩ q.2 := congrArg Prod.snd h
  apply Prod.ext
  · rw [← left_reconstruct_set p.1 p.2, ← left_reconstruct_set q.1 q.2, hL, hI]
  · rw [← right_reconstruct_set p.1 p.2, ← right_reconstruct_set q.1 q.2, hR, hI]

/-- The three code components are pairwise disjoint. -/
theorem cancellationCode_pairwiseDisjoint (S T : Finset F) :
    Disjoint (S \ T) (T \ S) ∧
      Disjoint (S \ T) (S ∩ T) ∧
      Disjoint (T \ S) (S ∩ T) := by
  refine ⟨disjoint_sdiff_sdiff S T, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hi).2
  · rw [Finset.disjoint_left]
    intro x hx hi
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hi).1

/-- At depth `t`, the common intersection has the complementary size `r-t`. -/
theorem inter_card_eq_sub_of_depth
    {G : Finset F} {r t : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r t) :
    (p.1.1 ∩ p.2.1).card = r - t := by
  have hdepth : (p.1.1 \ p.2.1).card = t := (Finset.mem_filter.mp hp).2
  rw [Finset.card_sdiff] at hdepth
  have hle : (p.2.1 ∩ p.1.1).card ≤ p.1.1.card :=
    Finset.card_le_card Finset.inter_subset_right
  rw [endpoint_card p.1] at hdepth hle
  rw [Finset.inter_comm]
  omega

/-- The code of a depth-`t` accident has component sizes `t,t,r-t`. -/
theorem cancellationCode_component_cards
    {G : Finset F} {r t : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r t) :
    (p.1.1 \ p.2.1).card = t ∧
      (p.2.1 \ p.1.1).card = t ∧
      (p.1.1 ∩ p.2.1).card = r - t := by
  have hdepth : (p.1.1 \ p.2.1).card = t := (Finset.mem_filter.mp hp).2
  have hcards := card_sdiff_eq_card_sdiff_of_card_eq
    ((endpoint_card p.1).trans (endpoint_card p.2).symm)
  exact ⟨hdepth, hcards.symm.trans hdepth, inter_card_eq_sub_of_depth hp⟩

/-- Both cores remain inside `G`, and the common intersection lies outside both cores. -/
theorem cancellationCode_subsets
    {G : Finset F} {r : ℕ}
    (p : SubsetFamily G r × SubsetFamily G r) :
    p.1.1 \ p.2.1 ⊆ G ∧ p.2.1 \ p.1.1 ⊆ G ∧ p.1.1 ∩ p.2.1 ⊆ G := by
  have hS : p.1.1 ⊆ G := (Finset.mem_powersetCard.mp p.1.2).1
  have hT : p.2.1 ⊆ G := (Finset.mem_powersetCard.mp p.2.2).1
  exact ⟨Finset.Subset.trans Finset.sdiff_subset hS,
    Finset.Subset.trans Finset.sdiff_subset hT,
    Finset.Subset.trans Finset.inter_subset_left hS⟩

/-- The core sums of every accident agree. -/
theorem cancellationCode_core_sums_eq
    {G : Finset F} {r t : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r t) :
    ∑ x ∈ p.1.1 \ p.2.1, x = ∑ x ∈ p.2.1 \ p.1.1, x := by
  have hpacc := (Finset.mem_filter.mp hp).1
  have hsum := (mem_subsetAccidents_iff.mp hpacc).1
  exact sum_sdiff_eq_sum_sdiff_of_sum_eq hsum

/-- **G144 capstone.** A depth-`t` accident has an injective three-component code with exactly the
structural data needed for the corrected lower-depth count. -/
theorem depthStratum_code_package
    {G : Finset F} {r t : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r t) :
    Disjoint (p.1.1 \ p.2.1) (p.2.1 \ p.1.1) ∧
      Disjoint (p.1.1 \ p.2.1) (p.1.1 ∩ p.2.1) ∧
      Disjoint (p.2.1 \ p.1.1) (p.1.1 ∩ p.2.1) ∧
      (p.1.1 \ p.2.1).card = t ∧
      (p.2.1 \ p.1.1).card = t ∧
      (p.1.1 ∩ p.2.1).card = r - t ∧
      (∑ x ∈ p.1.1 \ p.2.1, x = ∑ x ∈ p.2.1 \ p.1.1, x) := by
  obtain ⟨hdLR, hdLI, hdRI⟩ := cancellationCode_pairwiseDisjoint p.1.1 p.2.1
  obtain ⟨hcL, hcR, hcI⟩ := cancellationCode_component_cards hp
  exact ⟨hdLR, hdLI, hdRI, hcL, hcR, hcI, cancellationCode_core_sums_eq hp⟩

#print axioms cancellationCode_injective
#print axioms cancellationCode_pairwiseDisjoint
#print axioms inter_card_eq_sub_of_depth
#print axioms cancellationCode_component_cards
#print axioms cancellationCode_subsets
#print axioms cancellationCode_core_sums_eq
#print axioms depthStratum_code_package

end ArkLib.ProximityGap.Frontier.G144IntersectionAwareCancellationCode
