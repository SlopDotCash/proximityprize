/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87CorrectedPaddingDecoder

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

def wordSum {A B : Type*} [AddCommMonoid B] (ι : A → B) {n : ℕ}
    (word : Fin n → A) : B :=
  ∑ i, ι (word i)

abbrev EqualSumCorePair (A B : Type*) [AddCommMonoid B] (ι : A → B) (s : ℕ) :=
  {c : CorePair A s // wordSum ι c.1 = wordSum ι c.2}

def MaxCancellationCollisionSector (A B : Type*) [AddCommMonoid B] [DecidableEq A]
    (ι : A → B) (r s : ℕ) :=
  {x : EndpointPair A r //
    (G83MMaximalCommonCancellation.leftCore (valueBag x.1) (valueBag x.2)).card = s ∧
      wordSum ι x.1 = wordSum ι x.2}

theorem wordSum_assemble {A B : Type*} [AddCommMonoid B] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) :
    wordSum ι (assemble hsr e core pad) = wordSum ι core + wordSum ι pad := by
  have h := congrArg (fun m : Multiset A => (m.map ι).sum)
    (valueBag_assemble hsr e core pad)
  simpa [wordSum, valueBag, List.sum_ofFn] using h

theorem wordSum_comp_perm {A B : Type*} [AddCommMonoid B] (ι : A → B) {n : ℕ}
    (word : Fin n → A) (σ : Equiv.Perm (Fin n)) :
    wordSum ι (word ∘ σ) = wordSum ι word := by
  unfold wordSum
  exact Equiv.sum_comp σ (ι ∘ word)

noncomputable def decodeEqualSum {A B : Type*} [AddCommMonoid B] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    PaddingCode (EqualSumCorePair A B ι s) A r s → EndpointPair A r
  | ⟨cores, eLeft, eRight, pad, σ⟩ =>
      (assemble hsr eLeft cores.1.1 pad,
        assemble hsr eRight cores.1.2 (pad ∘ σ))

/-- Every equal-sum collision of maximal residual depth `s` has a corrected code whose core
coordinate itself satisfies the equal-sum equation. -/
theorem exists_equalSumCode_of_maximalDepth
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hdepth : (G83MMaximalCommonCancellation.leftCore
      (valueBag left) (valueBag right)).card = s)
    (hsum : wordSum ι left = wordSum ι right) :
    ∃ code : PaddingCode (EqualSumCorePair A B ι s) A r s,
      decodeEqualSum ι hsr code = (left, right) := by
  obtain ⟨code, hdecode⟩ := exists_code_of_maximalDepth hsr left right hdepth
  rcases code with ⟨cores, eLeft, eRight, pad, σ⟩
  have hleft : assemble hsr eLeft cores.1 pad = left := congrArg Prod.fst hdecode
  have hright : assemble hsr eRight cores.2 (pad ∘ σ) = right := congrArg Prod.snd hdecode
  have hcores : wordSum ι cores.1 = wordSum ι cores.2 := by
    apply add_right_cancel (b := wordSum ι pad)
    calc
      wordSum ι cores.1 + wordSum ι pad = wordSum ι left := by
        rw [← wordSum_assemble ι hsr eLeft cores.1 pad, hleft]
      _ = wordSum ι right := hsum
      _ = wordSum ι cores.2 + wordSum ι (pad ∘ σ) := by
        rw [← wordSum_assemble ι hsr eRight cores.2 (pad ∘ σ), hright]
      _ = wordSum ι cores.2 + wordSum ι pad := by rw [wordSum_comp_perm]
  refine ⟨⟨⟨cores, hcores⟩, eLeft, eRight, pad, σ⟩, ?_⟩
  exact hdecode

noncomputable instance equalSumCorePairFintype
    (A B : Type*) [AddCommMonoid B] [Fintype A] (ι : A → B) (s : ℕ) :
    Fintype (EqualSumCorePair A B ι s) := by
  classical
  letI : Finite (EqualSumCorePair A B ι s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- Elementary fiber saving: equal-sum ordered core pairs cost at most `n^(2s-1)`. -/
theorem card_equalSumCorePair_le
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] (ι : A → B)
    (hι : Function.Injective ι) {s : ℕ} (hs : 1 ≤ s) :
    Fintype.card (EqualSumCorePair A B ι s) ≤ (Fintype.card A) ^ (2 * s - 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  let enc : EqualSumCorePair A B ι (k + 1) →
      (Fin (k + 1) → A) × (Fin k → A) :=
    fun c => (c.1.1, fun j => c.1.2 j.castSucc)
  have henc : Function.Injective enc := by
    intro c d hcd
    change (c.1.1, fun j : Fin k => c.1.2 j.castSucc) =
      (d.1.1, fun j : Fin k => d.1.2 j.castSucc) at hcd
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => z.1) hcd
    · funext i
      refine Fin.lastCases ?_ (fun j => congrFun (congrArg Prod.snd hcd) j) i
      have hleft : c.1.1 = d.1.1 := congrArg (fun z => z.1) hcd
      have hinit : ∀ j : Fin k, c.1.2 j.castSucc = d.1.2 j.castSucc :=
        fun j => congrFun (congrArg Prod.snd hcd) j
      have hsums : ∑ j : Fin k, ι (c.1.2 j.castSucc) =
          ∑ j : Fin k, ι (d.1.2 j.castSucc) :=
        Finset.sum_congr rfl (fun j _ => congrArg ι (hinit j))
      have hright : wordSum ι c.1.2 = wordSum ι d.1.2 := by
        calc
          wordSum ι c.1.2 = wordSum ι c.1.1 := c.2.symm
          _ = wordSum ι d.1.1 := congrArg (wordSum ι) hleft
          _ = wordSum ι d.1.2 := d.2
      unfold wordSum at hright
      have ec := Fin.sum_univ_castSucc (fun i => ι (c.1.2 i))
      have ed := Fin.sum_univ_castSucc (fun i => ι (d.1.2 i))
      have hlast : ι (c.1.2 (Fin.last k)) = ι (d.1.2 (Fin.last k)) := by
        apply add_left_cancel (a := ∑ j : Fin k, ι (c.1.2 j.castSucc))
        calc
          (∑ j : Fin k, ι (c.1.2 j.castSucc)) + ι (c.1.2 (Fin.last k)) =
              ∑ i, ι (c.1.2 i) := ec.symm
          _ = ∑ i, ι (d.1.2 i) := hright
          _ = (∑ j : Fin k, ι (d.1.2 j.castSucc)) + ι (d.1.2 (Fin.last k)) := ed
          _ = (∑ j : Fin k, ι (c.1.2 j.castSucc)) + ι (d.1.2 (Fin.last k)) := by
            rw [hsums]
      exact hι hlast
  calc
    Fintype.card (EqualSumCorePair A B ι (k + 1)) ≤
        Fintype.card ((Fin (k + 1) → A) × (Fin k → A)) :=
      Fintype.card_le_of_injective enc henc
    _ = (Fintype.card A) ^ (2 * (k + 1) - 1) := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_add]
      congr 1
      omega

noncomputable def encodeCollisionSector
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    MaxCancellationCollisionSector A B ι r s →
      PaddingCode (EqualSumCorePair A B ι s) A r s :=
  fun x => Classical.choose
    (exists_equalSumCode_of_maximalDepth ι hsr x.1.1 x.1.2 x.2.1 x.2.2)

theorem decode_encodeCollisionSector
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r)
    (x : MaxCancellationCollisionSector A B ι r s) :
    decodeEqualSum ι hsr (encodeCollisionSector ι hsr x) = x.1 :=
  Classical.choose_spec
    (exists_equalSumCode_of_maximalDepth ι hsr x.1.1 x.1.2 x.2.1 x.2.2)

theorem encodeCollisionSector_injective
    {A B : Type*} [AddCancelCommMonoid B] [DecidableEq A] (ι : A → B)
    {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeCollisionSector ι hsr :
      MaxCancellationCollisionSector A B ι r s →
        PaddingCode (EqualSumCorePair A B ι s) A r s) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decode_encodeCollisionSector ι hsr x,
    ← decode_encodeCollisionSector ι hsr y, hxy]

noncomputable instance collisionSectorFintype
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (r s : ℕ) :
    Fintype (MaxCancellationCollisionSector A B ι r s) := by
  classical
  letI : Finite (MaxCancellationCollisionSector A B ι r s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- The actual equal-sum maximal-depth collision sector satisfies the elementary
`n^(2s-1)` factorial-corrected envelope. -/
theorem card_collisionSector_le_correctedCoreCount
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (r s : ℕ) (hsr : s ≤ r) :
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
      Fintype.card (EqualSumCorePair A B ι s) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (PaddingCode (EqualSumCorePair A B ι s) A r s) :=
      Fintype.card_le_of_injective (encodeCollisionSector ι hsr)
        (encodeCollisionSector_injective ι hsr)
    _ = _ := card_paddingCode (EqualSumCorePair A B ι s) A r s

/-- The actual equal-sum maximal-depth collision sector satisfies the elementary
`n^(2s-1)` factorial-corrected envelope. -/
theorem card_collisionSector_le_factorialCorrected
    (A B : Type*) [AddCancelCommMonoid B] [Fintype A] [DecidableEq A]
    (ι : A → B) (hι : Function.Injective ι)
    (r s : ℕ) (hsr : s ≤ r) (hs : 1 ≤ s) :
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
      (Fintype.card A) ^ (2 * s - 1) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (MaxCancellationCollisionSector A B ι r s) ≤
        Fintype.card (EqualSumCorePair A B ι s) * (r.descFactorial s) ^ 2 *
          (r - s).factorial * (Fintype.card A) ^ (r - s) :=
      card_collisionSector_le_correctedCoreCount A B ι r s hsr
    _ ≤ (Fintype.card A) ^ (2 * s - 1) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
      gcongr
      exact card_equalSumCorePair_le A B ι hι hs

end ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.wordSum_assemble
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.exists_equalSumCode_of_maximalDepth
#print axioms ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.card_equalSumCorePair_le
#print axioms
  ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.card_collisionSector_le_correctedCoreCount
#print axioms
  ArkLib.ProximityGap.Frontier.G88EqualSumCorrectedDecoder.card_collisionSector_le_factorialCorrected
