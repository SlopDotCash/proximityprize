/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G84CanonicalSlotsDepthFive
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G88EqualSumCorrectedDecoder

/-!
# G98: canonical increasing slots decode the actual collision sector

G84 replaced arbitrary core-position embeddings by their underlying position subsets, saving
`(s!)^2`, but left the concrete G87/G88 decoder weld open.  This file supplies that weld.

Every `s`-subset of `Fin r` has a canonical increasing enumeration.  Reading the endpoint at those
positions gives the canonically ordered core, while reading its complement gives padding.  Starting
from G88's occurrence-correct maximal-cancellation code, replacing each embedding by the increasing
enumeration of its range preserves the endpoint and merely permutes each residual core.  Hence the
two canonical cores still have equal sums, and the two canonical padding words still differ by one
permutation.

The final decoder is surjective onto the *actual* equal-sum maximal-cancellation sector.  No scaling
orbit quotient is used and no endpoint mass is discarded.  Consequently the G84 binomial-slot
cardinality bound applies unconditionally to the actual finite decoder.

Issue #505.  This closes a finite reconstruction obligation, not the depth-five energy estimate or
CORE.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G98CanonicalSlotCollisionDecoder

open G84CanonicalSlotsDepthFive
open G84SCorePaddingSlotPartition
open G84AEndpointAssembly
open G86CoreOccurrenceEmbedding
open G87CorrectedPaddingDecoder
open G88EqualSumCorrectedDecoder

/-- Canonical increasing embedding represented by a core-slot subset. -/
noncomputable def increasingEmbedding {r s : ℕ} (t : CoreSlots r s) : Fin s ↪ Fin r :=
  (t.1.orderEmbOfFin t.2).toEmbedding

/-- The increasing embedding has exactly the represented slot range. -/
theorem coreRange_increasingEmbedding {r s : ℕ} (t : CoreSlots r s) :
    coreRange (increasingEmbedding t) = t.1 := by
  ext x
  constructor
  · intro hx
    rw [coreRange, Finset.mem_map] at hx
    obtain ⟨i, hi, hix⟩ := hx
    rw [← hix]
    exact (t.1.orderIsoOfFin t.2 i).2
  · intro hx
    let y : t.1 := ⟨x, hx⟩
    obtain ⟨i, hi⟩ := (t.1.orderIsoOfFin t.2).surjective y
    rw [coreRange, Finset.mem_map]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    exact congrArg Subtype.val hi

/-- Forget the order of an embedding and retain only its range as canonical slot data. -/
def slotsOfEmbedding {r s : ℕ} (e : Fin s ↪ Fin r) : CoreSlots r s :=
  ⟨coreRange e, card_coreRange e⟩

@[simp] theorem coreRange_increasing_slotsOfEmbedding {r s : ℕ} (e : Fin s ↪ Fin r) :
    coreRange (increasingEmbedding (slotsOfEmbedding e)) = coreRange e := by
  exact coreRange_increasingEmbedding (slotsOfEmbedding e)

/-- Canonical endpoint assembly directly from subset-valued slot data. -/
noncomputable def canonicalAssemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (t : CoreSlots r s) (core : Fin s → A) (pad : Fin (r - s) → A) : Fin r → A :=
  assemble hsr (increasingEmbedding t) core pad

/-- Decode the canonical equal-sum code. -/
noncomputable def decodeCanonicalEqualSum
    {A B : Type*} [AddCommMonoid B] (ι : A → B) {r s : ℕ} (hsr : s ≤ r) :
    CanonicalPaddingCode (EqualSumCorePair A B ι s) A r s → EndpointPair A r
  | ⟨cores, slotsLeft, slotsRight, pad, σ⟩ =>
      (canonicalAssemble hsr slotsLeft cores.1.1 pad,
        canonicalAssemble hsr slotsRight cores.1.2 (pad ∘ σ))

/-- Canonical padding enumeration depends only on the core-position range. -/
theorem padSlots_eq_of_coreRange_eq {r s : ℕ} (hsr : s ≤ r)
    (e f : Fin s ↪ Fin r) (h : coreRange e = coreRange f) :
    padSlots hsr e = padSlots hsr f := by
  let ef : Fin (r - s) ↪o Fin r :=
    (coreRange f)ᶜ.orderEmbOfFin (by simp [Finset.card_compl, coreRange, hsr])
  have hefmem : ∀ i, ef i ∈ (coreRange e)ᶜ := by
    intro i
    rw [h]
    exact Finset.orderEmbOfFin_mem _ _ i
  have hef : ef =
      (coreRange e)ᶜ.orderEmbOfFin (by simp [Finset.card_compl, coreRange, hsr]) :=
    Finset.orderEmbOfFin_unique' _ hefmem
  unfold padSlots
  exact congrArg (fun g : Fin (r - s) ↪o Fin r => g.toEmbedding) hef.symm

/-- Replacing an embedding by the increasing enumeration of its range does not change the
canonical complement enumeration. -/
theorem padSlots_increasing_slotsOfEmbedding {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) :
    padSlots hsr (increasingEmbedding (slotsOfEmbedding e)) = padSlots hsr e :=
  padSlots_eq_of_coreRange_eq hsr _ _ (coreRange_increasing_slotsOfEmbedding e)

/-- Assembly from the values read at any core embedding and its canonical complement recovers the
whole endpoint. -/
theorem assemble_coreAt_paddingAt {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (word : Fin r → A) :
    assemble hsr e (coreAt e word) (paddingAt hsr e word) = word := by
  funext k
  cases h : (slotEquiv hsr e).symm k with
  | inl i =>
      have hk : k = e i := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact assemble_core hsr e (coreAt e word) (paddingAt hsr e word) i
  | inr j =>
      have hk : k = padSlots hsr e j := by
        have := congrArg (slotEquiv hsr e) h
        simpa using this
      subst k
      exact assemble_pad hsr e (coreAt e word) (paddingAt hsr e word) j

/-- **Canonical decoder surjectivity, pointwise form.** Every actual equal-sum collision at
maximal-cancellation depth `s` admits a code using only the two increasing core-slot subsets. -/
theorem exists_canonicalEqualSumCode_of_maximalDepth
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hdepth : (G83MMaximalCommonCancellation.leftCore
      (valueBag left) (valueBag right)).card = s)
    (hsum : wordSum ι left = wordSum ι right) :
    ∃ code : CanonicalPaddingCode (EqualSumCorePair A B ι s) A r s,
      decodeCanonicalEqualSum ι hsr code = (left, right) := by
  obtain ⟨code, hdecode⟩ :=
    exists_equalSumCode_of_maximalDepth ι hsr left right hdepth hsum
  rcases code with ⟨cores, eLeft, eRight, pad, σ⟩
  have hleft : assemble hsr eLeft cores.1.1 pad = left := congrArg Prod.fst hdecode
  have hright : assemble hsr eRight cores.1.2 (pad ∘ σ) = right := congrArg Prod.snd hdecode
  let slotsLeft := slotsOfEmbedding eLeft
  let slotsRight := slotsOfEmbedding eRight
  let incLeft := increasingEmbedding slotsLeft
  let incRight := increasingEmbedding slotsRight
  let coreLeft := coreAt incLeft left
  let coreRight := coreAt incRight right
  let padLeft := paddingAt hsr incLeft left
  let padRight := paddingAt hsr incRight right
  have hpadLeft : padLeft = pad := by
    funext j
    change left (padSlots hsr incLeft j) = pad j
    rw [show padSlots hsr incLeft = padSlots hsr eLeft by
      exact padSlots_increasing_slotsOfEmbedding hsr eLeft]
    rw [← hleft]
    exact assemble_pad hsr eLeft cores.1.1 pad j
  have hpadRight : padRight = pad ∘ σ := by
    funext j
    change right (padSlots hsr incRight j) = (pad ∘ σ) j
    rw [show padSlots hsr incRight = padSlots hsr eRight by
      exact padSlots_increasing_slotsOfEmbedding hsr eRight]
    rw [← hright]
    exact assemble_pad hsr eRight cores.1.2 (pad ∘ σ) j
  have hcoreSum : wordSum ι coreLeft = wordSum ι coreRight := by
    apply add_right_cancel (b := wordSum ι padLeft)
    calc
      wordSum ι coreLeft + wordSum ι padLeft = wordSum ι left := by
        rw [← wordSum_assemble ι hsr incLeft coreLeft padLeft,
          assemble_coreAt_paddingAt]
      _ = wordSum ι right := hsum
      _ = wordSum ι coreRight + wordSum ι padRight := by
        rw [← wordSum_assemble ι hsr incRight coreRight padRight,
          assemble_coreAt_paddingAt]
      _ = wordSum ι coreRight + wordSum ι padLeft := by
        rw [hpadLeft, hpadRight, wordSum_comp_perm]
  refine ⟨⟨⟨(coreLeft, coreRight), hcoreSum⟩, slotsLeft, slotsRight, padLeft, σ⟩, ?_⟩
  simp only [decodeCanonicalEqualSum, canonicalAssemble]
  apply Prod.ext
  · exact assemble_coreAt_paddingAt hsr incLeft left
  · have hp : padLeft ∘ σ = padRight := by rw [hpadLeft, hpadRight]
    change assemble hsr incRight coreRight (padLeft ∘ σ) = right
    rw [hp]
    exact assemble_coreAt_paddingAt hsr incRight right

/-- Choose a canonical-slot code for every element of the actual collision sector. -/
noncomputable def encodeCanonicalCollisionSector
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    MaxCancellationCollisionSector A B ι r s →
      CanonicalPaddingCode (EqualSumCorePair A B ι s) A r s :=
  fun x => Classical.choose
    (exists_canonicalEqualSumCode_of_maximalDepth ι hsr x.1.1 x.1.2 x.2.1 x.2.2)

theorem decode_encodeCanonicalCollisionSector
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (x : MaxCancellationCollisionSector A B ι r s) :
    decodeCanonicalEqualSum ι hsr (encodeCanonicalCollisionSector ι hsr x) = x.1 :=
  Classical.choose_spec
    (exists_canonicalEqualSumCode_of_maximalDepth ι hsr x.1.1 x.1.2 x.2.1 x.2.2)

/-- The chosen canonical code is injective because decoding recovers the original endpoint pair. -/
theorem encodeCanonicalCollisionSector_injective
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeCanonicalCollisionSector ι hsr :
      MaxCancellationCollisionSector A B ι r s →
        CanonicalPaddingCode (EqualSumCorePair A B ι s) A r s) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decode_encodeCanonicalCollisionSector ι hsr x,
    ← decode_encodeCanonicalCollisionSector ι hsr y, hxy]

/-- **G98 headline: actual canonical-slot collision-sector bound.** G84's `(s!)²` saving now
applies to the genuine G88 maximal-cancellation sector, with actual equal-sum core cardinality and
without a scaling quotient. -/
theorem card_collisionSector_le_canonical
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (r s : ℕ) (hsr : s ≤ r) :
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
      Fintype.card (EqualSumCorePair A B ι s) * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (CanonicalPaddingCode (EqualSumCorePair A B ι s) A r s) :=
      Fintype.card_le_of_injective (encodeCanonicalCollisionSector ι hsr)
        (encodeCanonicalCollisionSector_injective ι hsr)
    _ = _ := card_canonicalPaddingCode (EqualSumCorePair A B ι s) A r s

/-- Envelope-form restatement consumed directly by G84's production arithmetic. -/
theorem card_collisionSector_le_canonicalPadEnvelope
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (r s : ℕ) (hsr : s ≤ r) :
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
      canonicalPadEnvelope (Fintype.card A) r
        (Fintype.card (EqualSumCorePair A B ι s)) s := by
  simpa [canonicalPadEnvelope] using card_collisionSector_le_canonical A B ι r s hsr

/-- Elementary equal-sum fiber bound composed with the actual canonical decoder. -/
theorem card_collisionSector_le_canonical_elementary
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hι : Function.Injective ι)
    (r s : ℕ) (hsr : s ≤ r) (hs : 1 ≤ s) :
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
      (Fintype.card A) ^ (2 * s - 1) * (r.choose s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  calc
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (EqualSumCorePair A B ι s) * (r.choose s) ^ 2 *
          (r - s).factorial * (Fintype.card A) ^ (r - s) :=
      card_collisionSector_le_canonical A B ι r s hsr
    _ ≤ (Fintype.card A) ^ (2 * s - 1) * (r.choose s) ^ 2 *
          (r - s).factorial * (Fintype.card A) ^ (r - s) := by
      gcongr
      exact card_equalSumCorePair_le A B ι hι hs

/-- **Actual production depth-four weld.** Once the equal-sum depth-four core cardinality obeys
G84's fixed fourth-moment square estimate, the genuine maximal-cancellation collision sector fits
the production Wick budget.  The formerly open decoder hypothesis is discharged by G98. -/
theorem production_depth_four_actual_collisionSector_absorbed
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B)
    (hcard : Fintype.card A = productionN)
    (hcore : Fintype.card (EqualSumCorePair A B ι 4) ^ 2 ≤
      7600 ^ 2 * productionN ^ 13) :
    Fintype.card (MaxCancellationCollisionSector A B ι 110 4) ≤ productionWickBudget := by
  apply production_depth_four_canonical_absorbed
  · simpa [hcard] using
      card_collisionSector_le_canonicalPadEnvelope A B ι 110 4 (by omega)
  · exact hcore

#print axioms increasingEmbedding
#print axioms coreRange_increasingEmbedding
#print axioms coreRange_increasing_slotsOfEmbedding
#print axioms padSlots_eq_of_coreRange_eq
#print axioms padSlots_increasing_slotsOfEmbedding
#print axioms assemble_coreAt_paddingAt
#print axioms exists_canonicalEqualSumCode_of_maximalDepth
#print axioms decode_encodeCanonicalCollisionSector
#print axioms encodeCanonicalCollisionSector_injective
#print axioms card_collisionSector_le_canonical
#print axioms card_collisionSector_le_canonicalPadEnvelope
#print axioms card_collisionSector_le_canonical_elementary
#print axioms production_depth_four_actual_collisionSector_absorbed

end ArkLib.ProximityGap.Frontier.G98CanonicalSlotCollisionDecoder
