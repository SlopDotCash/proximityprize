/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G83MMaximalCommonCancellation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86CoreOccurrenceEmbedding
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G81CRelativePaddingOrderCeiling

/-!
# G87: the factorial-corrected padding decoder is surjective

This file packages canonical maximal multiset cancellation into the corrected G81C code.  For a
pair of length-`r` endpoints whose maximally cancelled residual has depth `s`, it:

1. orders the two residual multisets and the common multiset using `Multiset.toList`;
2. applies G86 to extract occurrence-correct core embeddings in both endpoints;
3. cancels the reconstructed core bags to prove the two complementary padding words have the same
   multiset;
4. uses G86's relative-permutation theorem for the final G81C coordinate.

Thus every genuine fixed-depth maximal-cancellation pair lies in the image of the
factorial-corrected decoder. Repeated values are handled occurrence-by-occurrence. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder

open G83MMaximalCommonCancellation
open G84AEndpointAssembly
open G84SCorePaddingSlotPartition
open G86CoreOccurrenceEmbedding
open G81CRelativePaddingOrderCeiling

def valueBag {A : Type*} {n : ℕ} (word : Fin n → A) : Multiset A :=
  (List.ofFn word : Multiset A)

noncomputable def bagWord {A : Type*} (m : Multiset A) : Fin m.card → A :=
  fun i => m.toList.get ⟨i.val, by simpa using i.isLt⟩

theorem valueBag_bagWord {A : Type*} (m : Multiset A) : valueBag (bagWord m) = m := by
  have hl : List.ofFn (bagWord m) = m.toList := by
    apply List.ext_get
    · simp [bagWord]
    · intro n hn hn'
      simp [bagWord]
  exact (congrArg (fun l : List A => (l : Multiset A)) hl).trans (Multiset.coe_toList m)

noncomputable def bagWordCast {A : Type*} (m : Multiset A) {n : ℕ}
    (h : m.card = n) : Fin n → A :=
  bagWord m ∘ Fin.cast h.symm

theorem valueBag_bagWordCast {A : Type*} (m : Multiset A) {n : ℕ}
    (h : m.card = n) : valueBag (bagWordCast m h) = m := by
  subst n
  simpa [bagWordCast] using valueBag_bagWord m

theorem valueBag_comp_equiv {A : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (f : κ → A) :
    (Multiset.map (f ∘ e) Finset.univ.val) = Multiset.map f Finset.univ.val := by
  rw [← Multiset.map_map]
  have hu := congrArg Finset.val (Finset.map_univ_equiv e)
  rw [Finset.map_val] at hu
  exact congrArg (Multiset.map f) (by simpa using hu)

theorem valueBag_eq_map {A : Type*} {n : ℕ} (word : Fin n → A) :
    valueBag word = Multiset.map word Finset.univ.val := by
  exact (Fin.univ_val_map word).symm

theorem valueBag_assemble {A : Type*} {r s : ℕ} (hsr : s ≤ r)
    (e : Fin s ↪ Fin r) (core : Fin s → A) (pad : Fin (r - s) → A) :
    valueBag (assemble hsr e core pad) = valueBag core + valueBag pad := by
  rw [valueBag_eq_map, valueBag_eq_map, valueBag_eq_map]
  rw [assemble, valueBag_comp_equiv (slotEquiv hsr e).symm]
  rw [← Finset.univ_disjSum_univ, Finset.val_disjSum, Multiset.map_disjSum]
  rfl

abbrev CorePair (A : Type*) (s : ℕ) := (Fin s → A) × (Fin s → A)
abbrev EndpointPair (A : Type*) (r : ℕ) := (Fin r → A) × (Fin r → A)

/-- Decode the corrected code into its two ordered endpoints. -/
noncomputable def decode {A : Type*} {r s : ℕ} (hsr : s ≤ r) :
    PaddingCode (CorePair A s) A r s → EndpointPair A r
  | ⟨cores, eLeft, eRight, pad, σ⟩ =>
      (assemble hsr eLeft cores.1 pad,
        assemble hsr eRight cores.2 (pad ∘ σ))

/-- The genuine maximal-cancellation sector of endpoint pairs with left residual depth `s`.
G83M proves the right residual has the same depth automatically. -/
def MaxCancellationSector (A : Type*) [DecidableEq A] (r s : ℕ) :=
  {x : EndpointPair A r //
    (leftCore (valueBag x.1) (valueBag x.2)).card = s}

/-- **Decoder surjectivity onto the genuine fixed-depth sector.** -/
theorem exists_code_of_maximalDepth
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (left right : Fin r → A)
    (hdepth : (leftCore (valueBag left) (valueBag right)).card = s) :
    ∃ code : PaddingCode (CorePair A s) A r s,
      decode hsr code = (left, right) := by
  let l := valueBag left
  let rr := valueBag right
  let lc := leftCore l rr
  let rc := rightCore l rr
  let p := commonPart l rr
  have hlcard : l.card = r := by simp [l, valueBag]
  have hrcard : rr.card = r := by simp [rr, valueBag]
  change lc.card = s at hdepth
  have hcoreR : rc.card = s := by
    calc
      rc.card = lc.card := (core_card_eq (hlcard.trans hrcard.symm)).symm
      _ = s := hdepth
  have hpad : p.card = r - s := by
    have h := congrArg Multiset.card (left_reconstruct l rr)
    simp only [Multiset.card_add] at h
    change lc.card + p.card = l.card at h
    omega
  let coreL : Fin s → A := bagWordCast lc hdepth
  let coreR : Fin s → A := bagWordCast rc hcoreR
  let pad0 : Fin (r - s) → A := bagWordCast p hpad
  have hbagCoreL : valueBag coreL = lc := valueBag_bagWordCast lc hdepth
  have hbagCoreR : valueBag coreR = rc := valueBag_bagWordCast rc hcoreR
  have hbagPad0 : valueBag pad0 = p := valueBag_bagWordCast p hpad
  have hsplitL : valueBag coreL + valueBag pad0 = valueBag left := by
    rw [hbagCoreL, hbagPad0]
    exact left_reconstruct l rr
  have hsplitR : valueBag coreR + valueBag pad0 = valueBag right := by
    rw [hbagCoreR, hbagPad0]
    exact right_reconstruct l rr
  obtain ⟨eLeft, hLeftCore, hLeftReconstruct⟩ :=
    exists_coreEmbedding_of_multiset_add hsr coreL pad0 left hsplitL
  obtain ⟨eRight, hRightCore, hRightReconstruct⟩ :=
    exists_coreEmbedding_of_multiset_add hsr coreR pad0 right hsplitR
  let padLeft := paddingAt hsr eLeft left
  let padRight := paddingAt hsr eRight right
  have hpadLeft : valueBag padLeft = p := by
    apply add_left_cancel (a := lc)
    calc
      lc + valueBag padLeft = valueBag coreL + valueBag padLeft := by rw [hbagCoreL]
      _ = valueBag left := by
        rw [← valueBag_assemble hsr eLeft coreL padLeft, hLeftReconstruct]
      _ = lc + p := (left_reconstruct l rr).symm
  have hpadRight : valueBag padRight = p := by
    apply add_left_cancel (a := rc)
    calc
      rc + valueBag padRight = valueBag coreR + valueBag padRight := by rw [hbagCoreR]
      _ = valueBag right := by
        rw [← valueBag_assemble hsr eRight coreR padRight, hRightReconstruct]
      _ = rc + p := (right_reconstruct l rr).symm
  obtain ⟨σ, hσ⟩ := exists_perm_comp_of_multiset_eq padLeft padRight
    (hpadLeft.trans hpadRight.symm)
  refine ⟨⟨(coreL, coreR), eLeft, eRight, padLeft, σ⟩, ?_⟩
  simp only [decode]
  apply Prod.ext
  · exact hLeftReconstruct
  · rw [← hσ]
    exact hRightReconstruct

/-- Choose one corrected code for each genuine maximal-cancellation pair. -/
noncomputable def encodeMaxCancellationSector
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r) :
    MaxCancellationSector A r s → PaddingCode (CorePair A s) A r s :=
  fun x => Classical.choose (exists_code_of_maximalDepth hsr x.1.1 x.1.2 x.2)

theorem decode_encodeMaxCancellationSector
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r)
    (x : MaxCancellationSector A r s) :
    decode hsr (encodeMaxCancellationSector hsr x) = x.1 :=
  Classical.choose_spec (exists_code_of_maximalDepth hsr x.1.1 x.1.2 x.2)

theorem encodeMaxCancellationSector_injective
    {A : Type*} [DecidableEq A] {r s : ℕ} (hsr : s ≤ r) :
    Function.Injective (encodeMaxCancellationSector hsr :
      MaxCancellationSector A r s → PaddingCode (CorePair A s) A r s) := by
  intro x y hxy
  apply Subtype.ext
  rw [← decode_encodeMaxCancellationSector hsr x,
    ← decode_encodeMaxCancellationSector hsr y, hxy]

noncomputable instance maxCancellationSectorFintype
    (A : Type*) [Fintype A] [DecidableEq A] (r s : ℕ) :
    Fintype (MaxCancellationSector A r s) := by
  classical
  letI : Finite (MaxCancellationSector A r s) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- **Actual factorial-corrected sector bound.** This is G81C's envelope with decoder
surjectivity discharged by canonical maximal cancellation. -/
theorem card_maxCancellationSector_le_factorialCorrected
    (A : Type*) [Fintype A] [DecidableEq A] (r s : ℕ) (hsr : s ≤ r) :
    Fintype.card (MaxCancellationSector A r s) ≤
      Fintype.card (CorePair A s) * (r.descFactorial s) ^ 2 *
        (r - s).factorial * (Fintype.card A) ^ (r - s) := by
  classical
  calc
    Fintype.card (MaxCancellationSector A r s) ≤
        Fintype.card (PaddingCode (CorePair A s) A r s) :=
      Fintype.card_le_of_injective (encodeMaxCancellationSector hsr)
        (encodeMaxCancellationSector_injective hsr)
    _ = _ := card_paddingCode (CorePair A s) A r s

end ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder.valueBag_bagWord
#print axioms ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder.valueBag_assemble
#print axioms ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder.exists_code_of_maximalDepth
#print axioms
  ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder.decode_encodeMaxCancellationSector
#print axioms
  ArkLib.ProximityGap.Frontier.G87CorrectedPaddingDecoder.card_maxCancellationSector_le_factorialCorrected
