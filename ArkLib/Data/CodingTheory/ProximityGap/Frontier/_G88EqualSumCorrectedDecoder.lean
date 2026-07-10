/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87CorrectedPaddingDecoder
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy

/-!
# G88: restrict the corrected decoder to equal-sum cores

For additive collisions, maximal common cancellation preserves equality of the two residual core
sums.  This file refines G87's decoder so its core coordinate is the higher additive-energy type,
not the unrestricted `n^(2s)` universe.  Its cardinality is at most `n^(2s-1)`, supplying the exact
factor of `n` needed by G82 at primitive depth three. Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder

open scoped BigOperators
open G87CorrectedPaddingDecoder
open G81CRelativePaddingOrderCeiling
open G84AEndpointAssembly

def wordSum {A : Type*} [AddCommMonoid A] {n : ℕ} (word : Fin n → A) : A :=
  ∑ i, word i

abbrev EqualSumCorePair (A : Type*) [AddCommMonoid A] (s : ℕ) :=
  {c : CorePair A s // wordSum c.1 = wordSum c.2}

def MaxCancellationCollisionSector (A : Type*) [AddCommMonoid A] [DecidableEq A]
    (r s : ℕ) :=
  {x : EndpointPair A r //
    (G83MMaximalCommonCancellation.leftCore (valueBag x.1) (valueBag x.2)).card = s ∧
      wordSum x.1 = wordSum x.2}

theorem wordSum_assemble {A : Type*} [AddCommMonoid A] {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) :
    wordSum (assemble hsr e core pad) = wordSum core + wordSum pad := by
  have h := congrArg Multiset.sum (valueBag_assemble hsr e core pad)
  simpa [wordSum, valueBag, List.sum_ofFn] using h

theorem wordSum_comp_perm {A : Type*} [AddCommMonoid A] {n : ℕ}
    (word : Fin n → A) (σ : Equiv.Perm (Fin n)) :
    wordSum (word ∘ σ) = wordSum word := by
  unfold wordSum
  exact Equiv.sum_comp σ word

noncomputable def decodeEqualSum {A : Type*} [AddCommMonoid A] {r s : ℕ} (hsr : s ≤ r) :
    PaddingCode (EqualSumCorePair A s) A r s → EndpointPair A r
  | ⟨cores, eLeft, eRight, pad, σ⟩ =>
      (assemble hsr eLeft cores.1.1 pad,
        assemble hsr eRight cores.1.2 (pad ∘ σ))

/-- Every equal-sum collision of maximal residual depth `s` has a corrected code whose core
coordinate itself satisfies the equal-sum equation. -/
theorem exists_equalSumCode_of_maximalDepth
    {A : Type*} [AddCancelCommMonoid A] [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hdepth : (G83MMaximalCommonCancellation.leftCore
      (valueBag left) (valueBag right)).card = s)
    (hsum : wordSum left = wordSum right) :
    ∃ code : PaddingCode (EqualSumCorePair A s) A r s,
      decodeEqualSum hsr code = (left, right) := by
  obtain ⟨code, hdecode⟩ := exists_code_of_maximalDepth hsr left right hdepth
  rcases code with ⟨cores, eLeft, eRight, pad, σ⟩
  have hleft : assemble hsr eLeft cores.1 pad = left := congrArg Prod.fst hdecode
  have hright : assemble hsr eRight cores.2 (pad ∘ σ) = right := congrArg Prod.snd hdecode
  have hcores : wordSum cores.1 = wordSum cores.2 := by
    apply add_right_cancel (b := wordSum pad)
    calc
      wordSum cores.1 + wordSum pad = wordSum left := by
        rw [← wordSum_assemble hsr eLeft cores.1 pad, hleft]
      _ = wordSum right := hsum
      _ = wordSum cores.2 + wordSum (pad ∘ σ) := by
        rw [← wordSum_assemble hsr eRight cores.2 (pad ∘ σ), hright]
      _ = wordSum cores.2 + wordSum pad := by rw [wordSum_comp_perm]
  refine ⟨⟨⟨cores, hcores⟩, eLeft, eRight, pad, σ⟩, ?_⟩
  exact hdecode

/-- The equal-sum core type is exactly the higher additive-energy fiber over the whole alphabet. -/
theorem card_equalSumCorePair_eq_addREnergy
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] (s : ℕ) :
    Fintype.card (EqualSumCorePair A s) =
      Finset.addREnergy s (Finset.univ : Finset A) := by
  classical
  rw [Finset.addREnergy_def]
  rw [Fintype.card_subtype]
  congr 1

/-- Elementary fiber saving: equal-sum ordered core pairs cost at most `n^(2s-1)`. -/
theorem card_equalSumCorePair_le
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] {s : ℕ} (hs : 1 ≤ s) :
    Fintype.card (EqualSumCorePair A s) ≤ (Fintype.card A) ^ (2 * s - 1) := by
  rw [card_equalSumCorePair_eq_addREnergy]
  simpa using Finset.addREnergy_le hs (Finset.univ : Finset A)

noncomputable def encodeCollisionSector
    {A : Type*} [AddCancelCommMonoid A] [DecidableEq A] {r s : ℕ} (hsr : s ≤ r) :
    MaxCancellationCollisionSector A r s →
      PaddingCode (EqualSumCorePair A s) A r s :=
  fun x => Classical.choose
    (exists_equalSumCode_of_maximalDepth hsr x.1.1 x.1.2 x.2.1 x.2.2)

theorem decode_encodeCollisionSector
    {A : Type*} [AddCancelCommMonoid A] [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (x : MaxCancellationCollisionSector A r s) :
    decodeEqualSum hsr (encodeCollisionSector hsr x) = x.1 :=
  Classical.choose_spec
    (exists_equalSumCode_of_maximalDepth hsr x.1.1 x.1.2 x.2.1 x.2.2)

theorem encodeCollisionSector_injective
    {A : Type*} [AddCancelCommMonoid A] [DecidableEq A] {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeCollisionSector hsr :
      MaxCancellationCollisionSector A r s →
        PaddingCode (EqualSumCorePair A s) A r s) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decode_encodeCollisionSector hsr x, ← decode_encodeCollisionSector hsr y, hxy]

noncomputable instance collisionSectorFintype
    (A : Type*) [AddCancelCommMonoid A] [Fintype A] [DecidableEq A] (r s : ℕ) :
    Fintype (MaxCancellationCollisionSector A r s) := by
  classical
  letI : Finite (MaxCancellationCollisionSector A r s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The actual equal-sum maximal-depth collision sector satisfies the elementary
`n^(2s-1)` factorial-corrected envelope. -/
theorem card_collisionSector_le_factorialCorrected
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A]
    (r s : ℕ) (hsr : s ≤ r) (hs : 1 ≤ s) :
    Fintype.card (MaxCancellationCollisionSector A r s) ≤
      (Fintype.card A) ^ (2 * s - 1) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (MaxCancellationCollisionSector A r s) ≤
        Fintype.card (PaddingCode (EqualSumCorePair A s) A r s) :=
      Fintype.card_le_of_injective (encodeCollisionSector hsr)
        (encodeCollisionSector_injective hsr)
    _ = Fintype.card (EqualSumCorePair A s) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) :=
      card_paddingCode (EqualSumCorePair A s) A r s
    _ ≤ (Fintype.card A) ^ (2 * s - 1) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
      gcongr
      exact card_equalSumCorePair_le A hs

end ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.wordSum_assemble
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.exists_equalSumCode_of_maximalDepth
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.card_equalSumCorePair_le
#print axioms
  ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.card_collisionSector_le_factorialCorrected
