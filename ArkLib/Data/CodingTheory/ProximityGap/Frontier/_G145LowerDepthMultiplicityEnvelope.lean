/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G144IntersectionAwareCancellationCode

/-!
# G145: the corrected lower-depth multiplicity envelope

G144 makes every depth-`t` accident inject into a disjoint equal-sum core pair plus a common
intersection.  For a fixed core pair, that intersection is an `(r-t)`-subset of the complement of
two disjoint `t`-sets, hence has at most

`choose (|G| - 2t) (r-t)`

choices.  This file proves the resulting census bound and then uses G143's canonical enumeration
to compare the core-pair census with `depthFiber G t t`.

This is the correct all-depth replacement for the false direct injection that forgets the common
intersection.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope

open scoped BigOperators
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G143DepthStratifiedSubsetAccidents
open ArkLib.ProximityGap.Frontier.G144IntersectionAwareCancellationCode

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

/-- Disjoint equal-sum pairs of `t`-subsets of `G`. -/
def subsetCorePairs (G : Finset F) (t : ℕ) : Finset (Finset F × Finset F) :=
  (G.powersetCard t ×ˢ G.powersetCard t).filter fun c =>
    Disjoint c.1 c.2 ∧ (∑ x ∈ c.1, x = ∑ x ∈ c.2, x) ∧ c.1 ≠ c.2

/-- Allowed common intersections for a fixed core pair. -/
def intersectionChoices (G : Finset F) (r t : ℕ) (c : Finset F × Finset F) :
    Finset (Finset F) :=
  (G \ (c.1 ∪ c.2)).powersetCard (r - t)

/-- All intersection-aware lift codes over all admissible core pairs. -/
def liftCodes (G : Finset F) (r t : ℕ) :
    Finset ((Finset F × Finset F) × Finset F) :=
  (subsetCorePairs G t).biUnion fun c =>
    (intersectionChoices G r t c).image fun I => (c, I)

/-- The G144 code of a subset-family pair. -/
def subsetCancellationCode {G : Finset F} {r : ℕ}
    (p : SubsetFamily G r × SubsetFamily G r) :
    (Finset F × Finset F) × Finset F :=
  cancellationCode (p.1.1, p.2.1)

theorem subsetCancellationCode_injective {G : Finset F} {r : ℕ} :
    Function.Injective (subsetCancellationCode :
      SubsetFamily G r × SubsetFamily G r → (Finset F × Finset F) × Finset F) := by
  intro p q h
  have hv : (p.1.1, p.2.1) = (q.1.1, q.2.1) := cancellationCode_injective h
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst hv
  · exact congrArg Prod.snd hv

theorem mem_subsetCorePairs_iff {G : Finset F} {t : ℕ} {c : Finset F × Finset F} :
    c ∈ subsetCorePairs G t ↔
      c.1 ∈ G.powersetCard t ∧ c.2 ∈ G.powersetCard t ∧
      Disjoint c.1 c.2 ∧ (∑ x ∈ c.1, x = ∑ x ∈ c.2, x) ∧ c.1 ≠ c.2 := by
  simp [subsetCorePairs, and_assoc]

/-- Every depth-stratum accident maps into the finite lift-code set. -/
theorem subsetCancellationCode_maps_stratum
    {G : Finset F} {r t : ℕ}
    {p : SubsetFamily G r × SubsetFamily G r}
    (hp : p ∈ subsetAccidentStratum G r t) :
    subsetCancellationCode p ∈ liftCodes G r t := by
  obtain ⟨hdLR, hdLI, hdRI, hcL, hcR, hcI, hsums⟩ := depthStratum_code_package hp
  have hne : p.1.1 \ p.2.1 ≠ p.2.1 \ p.1.1 := by
    intro heq
    have hself : Disjoint (p.1.1 \ p.2.1) (p.1.1 \ p.2.1) := by
      rwa [← heq] at hdLR
    have hzero : p.1.1 \ p.2.1 = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false]
      intro hx
      exact (Finset.disjoint_left.mp hself) hx hx
    have hpos := (accident_depth_pos_le (Finset.mem_filter.mp hp).1).1
    rw [subsetPairDepth, hzero, Finset.card_empty] at hpos
    omega
  obtain ⟨hLsub, hRsub, hIsub⟩ := cancellationCode_subsets p
  have hcore : (p.1.1 \ p.2.1, p.2.1 \ p.1.1) ∈ subsetCorePairs G t := by
    rw [mem_subsetCorePairs_iff]
    exact ⟨Finset.mem_powersetCard.mpr ⟨hLsub, hcL⟩,
      Finset.mem_powersetCard.mpr ⟨hRsub, hcR⟩, hdLR, hsums, hne⟩
  have hIavoid : p.1.1 ∩ p.2.1 ⊆
      G \ ((p.1.1 \ p.2.1) ∪ (p.2.1 \ p.1.1)) := by
    intro x hx
    refine Finset.mem_sdiff.mpr ⟨hIsub hx, ?_⟩
    intro hxc
    rw [Finset.mem_union] at hxc
    exact hxc.elim (fun h => Finset.disjoint_left.mp hdLI h hx)
      (fun h => Finset.disjoint_left.mp hdRI h hx)
  unfold liftCodes
  rw [Finset.mem_biUnion]
  refine ⟨(p.1.1 \ p.2.1, p.2.1 \ p.1.1), hcore, ?_⟩
  rw [Finset.mem_image]
  refine ⟨p.1.1 ∩ p.2.1, ?_, rfl⟩
  exact Finset.mem_powersetCard.mpr ⟨hIavoid, hcI⟩

/-- The depth stratum injects into the lift-code set. -/
theorem stratum_card_le_liftCodes (G : Finset F) (r t : ℕ) :
    (subsetAccidentStratum G r t).card ≤ (liftCodes G r t).card :=
  Finset.card_le_card_of_injOn subsetCancellationCode
    (fun _ hp => subsetCancellationCode_maps_stratum hp)
    (fun _ _ _ _ h => subsetCancellationCode_injective h)

/-- The complement of two disjoint `t`-cores has cardinality `|G|-2t`. -/
theorem core_complement_card {G : Finset F} {t : ℕ} {c : Finset F × Finset F}
    (hc : c ∈ subsetCorePairs G t) :
    (G \ (c.1 ∪ c.2)).card = G.card - 2 * t := by
  obtain ⟨hc1, hc2, hd, -, -⟩ := mem_subsetCorePairs_iff.mp hc
  obtain ⟨h1sub, h1card⟩ := Finset.mem_powersetCard.mp hc1
  obtain ⟨h2sub, h2card⟩ := Finset.mem_powersetCard.mp hc2
  have hunionSub : c.1 ∪ c.2 ⊆ G := Finset.union_subset h1sub h2sub
  rw [Finset.card_sdiff_of_subset hunionSub, Finset.card_union_of_disjoint hd, h1card, h2card]
  omega

theorem intersectionChoices_card {G : Finset F} {r t : ℕ}
    {c : Finset F × Finset F} (hc : c ∈ subsetCorePairs G t) :
    (intersectionChoices G r t c).card = (G.card - 2 * t).choose (r - t) := by
  rw [intersectionChoices, Finset.card_powersetCard, core_complement_card hc]

/-- The lift-code census has the corrected binomial envelope. -/
theorem liftCodes_card_le (G : Finset F) (r t : ℕ) :
    (liftCodes G r t).card ≤
      (subsetCorePairs G t).card * (G.card - 2 * t).choose (r - t) := by
  unfold liftCodes
  calc
    ((subsetCorePairs G t).biUnion fun c =>
        (intersectionChoices G r t c).image fun I => (c, I)).card
        ≤ ∑ c ∈ subsetCorePairs G t,
            ((intersectionChoices G r t c).image fun I => (c, I)).card :=
      Finset.card_biUnion_le
    _ = ∑ c ∈ subsetCorePairs G t, (G.card - 2 * t).choose (r - t) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [Finset.card_image_of_injective]
      · exact intersectionChoices_card hc
      · intro I J h
        exact congrArg Prod.snd h
    _ = (subsetCorePairs G t).card * (G.card - 2 * t).choose (r - t) := by
      simp [mul_comm]

/-- Core pairs canonically inject into the full-depth ordered-word fiber at depth `t`. -/
theorem corePairs_card_le_depthFiber (G : Finset F) (t : ℕ) :
    (subsetCorePairs G t).card ≤ depthFiber G t t := by
  have heq : (subsetCorePairs G t).card = (subsetAccidentStratum G t t).card := by
    refine Finset.card_bij
      (fun c hc =>
        (⟨c.1, (mem_subsetCorePairs_iff.mp hc).1⟩,
          ⟨c.2, (mem_subsetCorePairs_iff.mp hc).2.1⟩)) ?_ ?_ ?_
    · intro c hc
      rw [mem_fullDepth_stratum_iff, mem_subsetAccidents_iff]
      obtain ⟨hc1, hc2, hd, hs, hne⟩ := mem_subsetCorePairs_iff.mp hc
      exact ⟨⟨hs, fun h => hne (congrArg Subtype.val h)⟩, hd⟩
    · intro c hc d hd h
      exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
        (congrArg Subtype.val (congrArg Prod.snd h))
    · intro b hb
      refine ⟨(b.1.1, b.2.1), ?_, ?_⟩
      · rw [mem_subsetCorePairs_iff]
        obtain ⟨hbacc, hbdisj⟩ := mem_fullDepth_stratum_iff.mp hb
        obtain ⟨hbsum, hbne⟩ := mem_subsetAccidents_iff.mp hbacc
        refine ⟨b.1.2, b.2.2, hbdisj, hbsum, ?_⟩
        intro h
        exact hbne (Subtype.ext h)
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
  rw [heq]
  exact fullDepth_subsetAccidents_le_depthFiber G t

/-- **G145 capstone.** Correct all-depth multiplicity envelope. -/
theorem stratum_card_le_depthFiber_mul_choose (G : Finset F) (r t : ℕ) :
    (subsetAccidentStratum G r t).card ≤
      depthFiber G t t * (G.card - 2 * t).choose (r - t) := by
  exact (stratum_card_le_liftCodes G r t).trans
    ((liftCodes_card_le G r t).trans
      (Nat.mul_le_mul_right _ (corePairs_card_le_depthFiber G t)))

#print axioms subsetCancellationCode_maps_stratum
#print axioms stratum_card_le_liftCodes
#print axioms core_complement_card
#print axioms intersectionChoices_card
#print axioms liftCodes_card_le
#print axioms corePairs_card_le_depthFiber
#print axioms stratum_card_le_depthFiber_mul_choose

end ArkLib.ProximityGap.Frontier.G145LowerDepthMultiplicityEnvelope
