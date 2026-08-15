/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88EqualSumCorrectedDecoder
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G85EndpointAssemblyEquiv
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84CanonicalSlotCode

/-!
# G94: the genuine collision decoder uses canonical increasing core slots

G87/G88 proved surjectivity using arbitrary core embeddings, paying a descending factorial for
each endpoint.  The enumeration of an embedding's range is redundant: replace it by the unique
increasing enumeration, reread the core word in that order, and reread the complementary padding.
The endpoint equivalence reconstructs the same word, while occurrence matching supplies the one
relative padding permutation.

This file makes G84's binomial code apply to the actual equal-sum maximal-cancellation sector.
No orbit quotient or scaling saving is used. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder

open G84CanonicalSlotsDepthFive
open G84SCorePaddingSlotPartition
open G85EndpointAssemblyEquiv
open G86CoreOccurrenceEmbedding
open G87CorrectedPaddingDecoder
open G88EqualSumCorrectedDecoder

/-- Increasing enumeration of a stored core-position subset. -/
noncomputable def coreEmbedding {r s : ℕ} (t : CoreSlots r s) : Fin s ↪ Fin r :=
  (t.1.orderEmbOfFin t.2).toEmbedding

@[simp] theorem coreRange_coreEmbedding {r s : ℕ} (t : CoreSlots r s) :
    coreRange (coreEmbedding t) = t.1 := by
  simp [coreRange, coreEmbedding, t.1.map_orderEmbOfFin_univ t.2]

/-- The value multiset read through an embedding depends only on its range. -/
theorem valueBag_coreAt_eq_map_coreRange
    {A : Type*} {r s : ℕ} (e : Fin s ↪ Fin r) (word : Fin r → A) :
    valueBag (G85EndpointAssemblyEquiv.coreAt e word) =
      Multiset.map word (coreRange e).val := by
  rw [valueBag_eq_map]
  change Multiset.map (word ∘ e) Finset.univ.val = _
  rw [← Multiset.map_map]
  congr 1

theorem valueBag_coreAt_eq_of_coreRange_eq
    {A : Type*} {r s : ℕ} {e f : Fin s ↪ Fin r} (word : Fin r → A)
    (h : coreRange e = coreRange f) :
    valueBag (G85EndpointAssemblyEquiv.coreAt e word) =
      valueBag (G85EndpointAssemblyEquiv.coreAt f word) := by
  rw [valueBag_coreAt_eq_map_coreRange, valueBag_coreAt_eq_map_coreRange, h]

/-- Decode a binomial-position code into its two ordered endpoints. -/
noncomputable def decodeCanonical
    {A B : Type*} [AddCommMonoid B] (ι : A → B) {r s : ℕ} (hsr : s ≤ r) :
    CanonicalPaddingCode (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s →
      EndpointPair A r
  | ⟨cores, tLeft, tRight, pad, σ⟩ =>
      (G84AEndpointAssembly.assemble hsr (coreEmbedding tLeft) cores.1.1 pad,
        G84AEndpointAssembly.assemble hsr (coreEmbedding tRight) cores.1.2 (pad ∘ σ))

/-- Every genuine equal-sum maximal-cancellation collision has a canonical-slot code. -/
theorem exists_canonicalCode_of_collision
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (x : G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s) :
    ∃ code : CanonicalPaddingCode
      (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s,
      decodeCanonical ι hsr code = x.1 := by
  obtain ⟨old, hold⟩ := exists_equalSumCode_of_maximalDepth
    ι hsr x.1.1 x.1.2 x.2.1 x.2.2
  rcases old with ⟨oldCores, eLeft, eRight, oldPad, oldσ⟩
  have hleft : G84AEndpointAssembly.assemble hsr eLeft oldCores.1.1 oldPad = x.1.1 :=
    congrArg Prod.fst hold
  have hright : G84AEndpointAssembly.assemble hsr eRight oldCores.1.2 (oldPad ∘ oldσ) = x.1.2 :=
    congrArg Prod.snd hold
  let tLeft : CoreSlots r s := ⟨coreRange eLeft, card_coreRange eLeft⟩
  let tRight : CoreSlots r s := ⟨coreRange eRight, card_coreRange eRight⟩
  let ceLeft := coreEmbedding tLeft
  let ceRight := coreEmbedding tRight
  let coreLeft := G85EndpointAssemblyEquiv.coreAt ceLeft x.1.1
  let coreRight := G85EndpointAssemblyEquiv.coreAt ceRight x.1.2
  let padLeft := G85EndpointAssemblyEquiv.paddingAt hsr ceLeft x.1.1
  let padRight := G85EndpointAssemblyEquiv.paddingAt hsr ceRight x.1.2
  have holdCoreLeft : G85EndpointAssemblyEquiv.coreAt eLeft x.1.1 = oldCores.1.1 := by
    rw [← hleft]
    exact coreAt_assemble hsr eLeft oldCores.1.1 oldPad
  have holdCoreRight : G85EndpointAssemblyEquiv.coreAt eRight x.1.2 = oldCores.1.2 := by
    rw [← hright]
    exact coreAt_assemble hsr eRight oldCores.1.2 (oldPad ∘ oldσ)
  have hcoreBagLeft : valueBag coreLeft = valueBag oldCores.1.1 := by
    calc
      valueBag coreLeft = valueBag (G85EndpointAssemblyEquiv.coreAt eLeft x.1.1) := by
        apply valueBag_coreAt_eq_of_coreRange_eq x.1.1
        simp [ceLeft, tLeft]
      _ = valueBag oldCores.1.1 := congrArg valueBag holdCoreLeft
  have hcoreBagRight : valueBag coreRight = valueBag oldCores.1.2 := by
    calc
      valueBag coreRight = valueBag (G85EndpointAssemblyEquiv.coreAt eRight x.1.2) := by
        apply valueBag_coreAt_eq_of_coreRange_eq x.1.2
        simp [ceRight, tRight]
      _ = valueBag oldCores.1.2 := congrArg valueBag holdCoreRight
  have holdPadBag : valueBag (oldPad ∘ oldσ) = valueBag oldPad := by
    rw [valueBag_eq_map, valueBag_eq_map]
    exact valueBag_comp_equiv oldσ oldPad
  have hpadBagLeft : valueBag padLeft = valueBag oldPad := by
    apply add_left_cancel (a := valueBag coreLeft)
    calc
      valueBag coreLeft + valueBag padLeft = valueBag x.1.1 := by
        rw [← valueBag_assemble hsr ceLeft coreLeft padLeft,
          assemble_coreAt_paddingAt hsr ceLeft x.1.1]
      _ = valueBag oldCores.1.1 + valueBag oldPad := by
        rw [← valueBag_assemble hsr eLeft oldCores.1.1 oldPad, hleft]
      _ = valueBag coreLeft + valueBag oldPad := by rw [hcoreBagLeft]
  have hpadBagRight : valueBag padRight = valueBag oldPad := by
    apply add_left_cancel (a := valueBag coreRight)
    calc
      valueBag coreRight + valueBag padRight = valueBag x.1.2 := by
        rw [← valueBag_assemble hsr ceRight coreRight padRight,
          assemble_coreAt_paddingAt hsr ceRight x.1.2]
      _ = valueBag oldCores.1.2 + valueBag (oldPad ∘ oldσ) := by
        rw [← valueBag_assemble hsr eRight oldCores.1.2 (oldPad ∘ oldσ), hright]
      _ = valueBag oldCores.1.2 + valueBag oldPad := by rw [holdPadBag]
      _ = valueBag coreRight + valueBag oldPad := by rw [hcoreBagRight]
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_multiset_eq padLeft padRight
    (hpadBagLeft.trans hpadBagRight.symm)
  have hcoreSum : wordSum ι coreLeft = wordSum ι coreRight := by
    apply add_right_cancel (b := wordSum ι padLeft)
    calc
      wordSum ι coreLeft + wordSum ι padLeft = wordSum ι x.1.1 := by
        rw [← wordSum_assemble ι hsr ceLeft coreLeft padLeft,
          assemble_coreAt_paddingAt hsr ceLeft x.1.1]
      _ = wordSum ι x.1.2 := x.2.2
      _ = wordSum ι coreRight + wordSum ι padRight := by
        rw [← wordSum_assemble ι hsr ceRight coreRight padRight,
          assemble_coreAt_paddingAt hsr ceRight x.1.2]
      _ = wordSum ι coreRight + wordSum ι padLeft := by
        rw [hσ, wordSum_comp_perm]
  refine ⟨⟨⟨(coreLeft, coreRight), hcoreSum⟩, tLeft, tRight, padLeft, σ⟩, ?_⟩
  apply Prod.ext
  · simpa only [decodeCanonical] using assemble_coreAt_paddingAt hsr ceLeft x.1.1
  · simp only [decodeCanonical]
    rw [← hσ]
    exact assemble_coreAt_paddingAt hsr ceRight x.1.2

noncomputable def encodeCanonical
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s →
      CanonicalPaddingCode (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s :=
  fun x ↦ Classical.choose (exists_canonicalCode_of_collision ι hsr x)

theorem encodeCanonical_injective
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeCanonical ι hsr :
      G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s →
      CanonicalPaddingCode (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s) := by
  intro x y hxy
  apply Subtype.ext
  have hx := Classical.choose_spec (exists_canonicalCode_of_collision ι hsr x)
  have hy := Classical.choose_spec (exists_canonicalCode_of_collision ι hsr y)
  have hxy' : Classical.choose (exists_canonicalCode_of_collision ι hsr x) =
      Classical.choose (exists_canonicalCode_of_collision ι hsr y) := by
    simpa only [encodeCanonical] using hxy
  rw [← hx, ← hy, hxy']

/-- **Actual canonical-slot sector bound.** -/
theorem card_collisionSector_le_canonical
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (r s : ℕ) (hsr : s ≤ r) :
    Fintype.card (G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s) ≤
      Fintype.card (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (CanonicalPaddingCode
          (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s) :=
      Fintype.card_le_of_injective (encodeCanonical ι hsr) (encodeCanonical_injective ι hsr)
    _ = _ := card_canonicalPaddingCode
      (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) A r s

/-- Actual canonical decoder plus the elementary equal-sum fiber bound. -/
theorem card_collisionSector_le_canonical_fiber
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hι : Function.Injective ι)
    (r s : ℕ) (hsr : s ≤ r) (hs : 1 ≤ s) :
    Fintype.card (G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s) ≤
      (Fintype.card A) ^ (2 * s - 1) * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  calc
    Fintype.card (G88EqualSumCorrectedDecoder.MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (G88EqualSumCorrectedDecoder.EqualSumCorePair A B ι s) *
          (r.choose s) ^ 2 * (r - s).factorial * (Fintype.card A) ^ (r - s) :=
      card_collisionSector_le_canonical A B ι r s hsr
    _ ≤ (Fintype.card A) ^ (2 * s - 1) * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
      gcongr
      exact card_equalSumCorePair_le A B ι hι hs

end ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder.coreRange_coreEmbedding
#print axioms ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder.exists_canonicalCode_of_collision
#print axioms ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder.card_collisionSector_le_canonical
#print axioms
  ArkLib.ProximityGap.Frontier.G94CanonicalSlotDecoder.card_collisionSector_le_canonical_fiber
