/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.HammingBallVolumeBasics
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.EntropyVolumeUpperBall

/-!
# Elias list-size ≤ ball-volume bound

The number of `δ`-close codewords to a word is at most the q-ary Hamming-ball volume `Vol_q(δ,n)`,
in three forms: per-word (`closeCodewordsRel_ncard_le_hammingBallVolume`), maximised
`|Λ(C,δ)| ≤ Vol_q(δ,n)` (`Lambda_le_hammingBallVolume`), and as a `listDecodable` statement
(`listDecodable_hammingBallVolume`).  This is the elementary Elias upper bound: the close-codeword
set sits inside the radius-`⌊δn⌋` Hamming ball, whose cardinality is exactly the volume
(`hammingBallVolume_eq_ncard_hammingBall`).
-/

open ListDecodable

namespace CodingTheory

/-- **Elias upper bound (per-word).** The number of `δ`-close codewords of any code `C` to a word
`f` is at most the q-ary Hamming-ball volume `Vol_q(δ, n)`. -/
theorem closeCodewordsRel_ncard_le_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (f : ι → F) (δ : ℝ) :
    (closeCodewordsRel C f δ).ncard ≤ hammingBallVolume (Fintype.card F) δ (Fintype.card ι) := by
  rw [hammingBallVolume_eq_ncard_hammingBall δ f]
  refine Set.ncard_le_ncard (fun c hc => ?_) (Set.toFinite _)
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hball := hc.2
  simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist] at hball
  push_cast at hball
  rw [div_le_iff₀ hn] at hball
  simp only [hammingBall, Set.mem_setOf_eq]
  exact Nat.le_floor hball

/-- **Maximised Elias bound `|Λ(C,δ)| ≤ Vol_q(δ,n)`.** -/
theorem Lambda_le_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ) :
    Lambda C δ ≤ (hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℕ∞) := by
  apply Lambda_le_natCast_of_forall_ncard_le
  intro f
  exact closeCodewordsRel_ncard_le_hammingBallVolume C f δ

/-- **Every code is `(δ, Vol_q(δ,n))`-list-decodable** — the `listDecodable`-predicate form. -/
theorem listDecodable_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ) :
    listDecodable C δ ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℕ) : ℝ) := by
  intro y
  exact_mod_cast closeCodewordsRel_ncard_le_hammingBallVolume C y δ

/-- **Maximised Elias entropy upper bound, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem Lambda_le_qEntropy_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    (Lambda C δ : ENNReal) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
        (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card A)
            ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) := by
  have hΛ : (Lambda C δ : ENNReal) ≤
      ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ∞) : ENNReal) :=
    ENat.toENNReal_mono (Lambda_le_hammingBallVolume C δ)
  have hcast :
      ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ∞) : ENNReal) =
        ENNReal.ofReal ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    simp
  have hvol := hammingBallVolume_le_qEntropy_card_generic (ι := ι) (A := A) δ hr hcap hq
  rw [hcast] at hΛ
  exact le_trans hΛ (ENNReal.ofReal_le_ofReal hvol)

/-- **Maximised Elias entropy upper bound, finite-domain form.**  The exact floor-radius
Hamming-ball entropy estimate gives a direct real-valued bound on `Λ(C,δ)`. -/
theorem Lambda_le_qEntropy_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (Lambda C δ : ENNReal) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
        (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card F)
            ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) :=
  Lambda_le_qEntropy_card_generic (ι := ι) (A := F) C δ hr hcap Fintype.one_lt_card

/-- **Per-word Elias entropy upper bound, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem closeCodewordsRel_ncard_le_qEntropy_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (f : ι → A) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    ((closeCodewordsRel C f δ).ncard : ℝ) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card A)
            ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))) := by
  have hcount :
      (closeCodewordsRel C f δ).ncard ≤
        hammingBallVolume (Fintype.card A) δ (Fintype.card ι) :=
    closeCodewordsRel_ncard_le_hammingBallVolume C f δ
  have hvol := hammingBallVolume_le_qEntropy_card_generic (ι := ι) (A := A) δ hr hcap hq
  exact le_trans (by exact_mod_cast hcount) hvol

/-- **Per-word Elias entropy upper bound, finite-domain form.** -/
theorem closeCodewordsRel_ncard_le_qEntropy_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (f : ι → F) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    ((closeCodewordsRel C f δ).ncard : ℝ) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card F)
            ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ))) :=
  closeCodewordsRel_ncard_le_qEntropy_card_generic (ι := ι) (A := F) C f δ hr hcap Fintype.one_lt_card

/-- **List-decodability from the finite-domain floor-radius entropy bound, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem listDecodable_qEntropy_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    listDecodable C δ (((Fintype.card ι : ℝ) + 1) *
      (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
        qEntropy (Fintype.card A)
          ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) := by
  intro y
  exact closeCodewordsRel_ncard_le_qEntropy_card_generic C y δ hr hcap hq

/-- **List-decodability from the finite-domain floor-radius entropy bound.** -/
theorem listDecodable_qEntropy_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    listDecodable C δ (((Fintype.card ι : ℝ) + 1) *
      (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
        qEntropy (Fintype.card F)
          ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) :=
  listDecodable_qEntropy_card_generic (ι := ι) (A := F) C δ hr hcap Fintype.one_lt_card

/-- **Maximised Elias entropy upper bound with the real radius exponent, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem Lambda_le_qEntropy_real_radius_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    (Lambda C δ : ENNReal) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
        (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card A) δ)) := by
  have hΛ : (Lambda C δ : ENNReal) ≤
      ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ∞) : ENNReal) :=
    ENat.toENNReal_mono (Lambda_le_hammingBallVolume C δ)
  have hcast :
      ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ∞) : ENNReal) =
        ENNReal.ofReal ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℕ) : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    simp
  have hvol := hammingBallVolume_le_qEntropy_real_radius_card_generic
    (ι := ι) (A := A) δ hδ0 hδ hq
  rw [hcast] at hΛ
  exact le_trans hΛ (ENNReal.ofReal_le_ofReal hvol)

/-- **Maximised Elias entropy upper bound with the real radius exponent.**  Below capacity, the
finite-domain floor-radius bound can be relaxed to the cleaner exponent `H_q(δ)`. -/
theorem Lambda_le_qEntropy_real_radius_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (Lambda C δ : ENNReal) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
        (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card F) δ)) :=
  Lambda_le_qEntropy_real_radius_card_generic (ι := ι) (A := F) C δ hδ0 hδ Fintype.one_lt_card

/-- **Per-word Elias entropy upper bound with the real radius exponent, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem closeCodewordsRel_ncard_le_qEntropy_real_radius_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (f : ι → A) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    ((closeCodewordsRel C f δ).ncard : ℝ) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card A) δ) := by
  have hcount :
      (closeCodewordsRel C f δ).ncard ≤
        hammingBallVolume (Fintype.card A) δ (Fintype.card ι) :=
    closeCodewordsRel_ncard_le_hammingBallVolume C f δ
  have hvol := hammingBallVolume_le_qEntropy_real_radius_card_generic
    (ι := ι) (A := A) δ hδ0 hδ hq
  exact le_trans (by exact_mod_cast hcount) hvol

/-- **Per-word Elias entropy upper bound with the real radius exponent.** -/
theorem closeCodewordsRel_ncard_le_qEntropy_real_radius_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (f : ι → F) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    ((closeCodewordsRel C f δ).ncard : ℝ) ≤
      ((Fintype.card ι : ℝ) + 1) *
        (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
          qEntropy (Fintype.card F) δ) :=
  closeCodewordsRel_ncard_le_qEntropy_real_radius_card_generic (ι := ι) (A := F) C f δ hδ0 hδ Fintype.one_lt_card

/-- **List-decodability from the finite-domain real-radius entropy bound, generic alphabet form.**  The `Field` wrapper below is the `A = F` specialization. -/
theorem listDecodable_qEntropy_real_radius_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    listDecodable C δ (((Fintype.card ι : ℝ) + 1) *
      (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
        qEntropy (Fintype.card A) δ)) := by
  intro y
  exact closeCodewordsRel_ncard_le_qEntropy_real_radius_card_generic C y δ hδ0 hδ hq

/-- **List-decodability from the finite-domain real-radius entropy bound.** -/
theorem listDecodable_qEntropy_real_radius_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    listDecodable C δ (((Fintype.card ι : ℝ) + 1) *
      (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
        qEntropy (Fintype.card F) δ)) :=
  listDecodable_qEntropy_real_radius_card_generic (ι := ι) (A := F) C δ hδ0 hδ Fintype.one_lt_card

/-- **List-size lower bound `1 ≤ |Λ(C,δ)|` for a nonempty code and `δ ≥ 0`.** Any codeword is
`0`-close to itself, so it lies in its own close-codeword list; with `Lambda_le_hammingBallVolume`
this brackets `1 ≤ |Λ(C,δ)| ≤ Vol_q(δ,n)`. -/
theorem one_le_Lambda_of_nonempty {ι : Type} [Fintype ι] {F : Type} [Fintype F] [DecidableEq F]
    {C : Code ι F} (hC : C.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) : 1 ≤ Lambda C δ := by
  obtain ⟨c, hc⟩ := hC
  have hmem : c ∈ closeCodewordsRel C c δ := by
    refine ⟨hc, ?_⟩
    simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist, hammingDist_self,
      Nat.cast_zero, zero_div, NNRat.cast_zero]
    exact hδ
  have h1 : 0 < (closeCodewordsRel C c δ).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨c, hmem⟩
  calc (1 : ℕ∞) ≤ ((closeCodewordsRel C c δ).ncard : ℕ∞) := by
        have h1' : 1 ≤ (closeCodewordsRel C c δ).ncard := h1
        exact_mod_cast h1'
    _ ≤ Lambda C δ := by
        unfold Lambda
        exact le_iSup (fun f => ((closeCodewordsRel C f δ).ncard : ℕ∞)) c

/-- **Two-sided nonempty list-size bracket with the exact Hamming-ball volume.** -/
theorem one_le_Lambda_and_Lambda_le_hammingBallVolume
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Fintype F]
    [DecidableEq F] (C : Code ι F) (hC : C.Nonempty) (δ : ℝ) (hδ : 0 ≤ δ) :
    (1 : ℕ∞) ≤ Lambda C δ ∧
      Lambda C δ ≤ (hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℕ∞) := by
  exact ⟨one_le_Lambda_of_nonempty (C := C) hC hδ, Lambda_le_hammingBallVolume C δ⟩

/-- **Two-sided nonempty list-size bracket with the exact floor-radius entropy exponent, generic form.** -/
theorem one_le_Lambda_and_Lambda_le_qEntropy_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (hC : C.Nonempty) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    (1 : ENNReal) ≤ (Lambda C δ : ENNReal) ∧
      (Lambda C δ : ENNReal) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
          (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
            qEntropy (Fintype.card A)
              ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) := by
  refine ⟨?_, Lambda_le_qEntropy_card_generic C δ hr hcap hq⟩
  simpa using ENat.toENNReal_mono (one_le_Lambda_of_nonempty (C := C) hC hδ0)

/-- **Two-sided nonempty list-size bracket with the exact floor-radius entropy exponent.** -/
theorem one_le_Lambda_and_Lambda_le_qEntropy_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (hC : C.Nonempty) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hr : ⌊δ * (Fintype.card ι : ℝ)⌋₊ < Fintype.card ι)
    (hcap :
      (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)
        ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (1 : ENNReal) ≤ (Lambda C δ : ENNReal) ∧
      (Lambda C δ : ENNReal) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
          (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
            qEntropy (Fintype.card F)
              ((⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ) / (Fintype.card ι : ℝ)))) :=
  one_le_Lambda_and_Lambda_le_qEntropy_card_generic (ι := ι) (A := F) C hC δ hδ0 hr hcap Fintype.one_lt_card

/-- **Two-sided nonempty list-size bracket with the relaxed real-radius entropy exponent, generic form.** -/
theorem one_le_Lambda_and_Lambda_le_qEntropy_real_radius_card_generic
    {ι A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (C : Code ι A) (hC : C.Nonempty) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card A : ℝ))
    (hq : 2 ≤ Fintype.card A) :
    (1 : ENNReal) ≤ (Lambda C δ : ENNReal) ∧
      (Lambda C δ : ENNReal) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
          (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) *
            qEntropy (Fintype.card A) δ)) := by
  refine ⟨?_, Lambda_le_qEntropy_real_radius_card_generic C δ hδ0 hδ hq⟩
  simpa using ENat.toENNReal_mono (one_le_Lambda_of_nonempty (C := C) hC hδ0)

/-- **Two-sided nonempty list-size bracket with the relaxed real-radius entropy exponent.** -/
theorem one_le_Lambda_and_Lambda_le_qEntropy_real_radius_card
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : Code ι F) (hC : C.Nonempty) (δ : ℝ)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 - 1 / (Fintype.card F : ℝ)) :
    (1 : ENNReal) ≤ (Lambda C δ : ENNReal) ∧
      (Lambda C δ : ENNReal) ≤
        ENNReal.ofReal (((Fintype.card ι : ℝ) + 1) *
          (Fintype.card F : ℝ) ^ ((Fintype.card ι : ℝ) *
            qEntropy (Fintype.card F) δ)) :=
  one_le_Lambda_and_Lambda_le_qEntropy_real_radius_card_generic (ι := ι) (A := F) C hC δ hδ0 hδ Fintype.one_lt_card

/-- **Every code is uniquely decodable at radius 0** — the radius-0 list has at most
`Vol_q(0,n) = 1` codeword (the Elias bound `listDecodable_hammingBallVolume` at `δ = 0`). -/
theorem uniqueDecodable_zero {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [DecidableEq F] (C : Code ι F) : uniqueDecodable C 0 := by
  have h := listDecodable_hammingBallVolume C (0 : ℝ)
  rwa [hammingBallVolume_zero_radius, Nat.cast_one] at h

/-- **List size never exceeds the whole space `|Λ(C,δ)| ≤ q^n`**, chaining the maximised Elias bound
with the whole-space volume ceiling `hammingBallVolume_le_qpow`. -/
theorem Lambda_le_qpow {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Nonempty F] [DecidableEq F] (C : Code ι F) (δ : ℝ) :
    Lambda C δ ≤ ((Fintype.card F ^ Fintype.card ι : ℕ) : ℕ∞) := by
  refine le_trans (Lambda_le_hammingBallVolume C δ) ?_
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  exact_mod_cast hammingBallVolume_le_qpow (Fintype.card F) hq δ (Fintype.card ι)

/-- **Two-sided nonempty list-size bracket with the whole ambient word-space bound.** -/
theorem one_le_Lambda_and_Lambda_le_qpow
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Nonempty F] [DecidableEq F]
    (C : Code ι F) (hC : C.Nonempty) (δ : ℝ) (hδ : 0 ≤ δ) :
    (1 : ℕ∞) ≤ Lambda C δ ∧
      Lambda C δ ≤ ((Fintype.card F ^ Fintype.card ι : ℕ) : ℕ∞) := by
  exact ⟨one_le_Lambda_of_nonempty (C := C) hC hδ, Lambda_le_qpow C δ⟩

/-- **Per-word whole-space list-size bound.**  Every close-codeword list is contained in the
ambient word space, so its size is at most `q^n`. -/
theorem closeCodewordsRel_ncard_le_qpow {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Nonempty F] [DecidableEq F]
    (C : Code ι F) (f : ι → F) (δ : ℝ) :
    (closeCodewordsRel C f δ).ncard ≤ Fintype.card F ^ Fintype.card ι := by
  refine le_trans (closeCodewordsRel_ncard_le_hammingBallVolume C f δ) ?_
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  exact hammingBallVolume_le_qpow (Fintype.card F) hq δ (Fintype.card ι)

/-- **Every code is `(δ, q^n)`-list-decodable.**  This is the predicate form of the
whole-space per-word close-list bound. -/
theorem listDecodable_qpow {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Nonempty F] [DecidableEq F] (C : Code ι F) (δ : ℝ) :
    listDecodable C δ ((Fintype.card F ^ Fintype.card ι : ℕ) : ℝ) := by
  intro y
  exact_mod_cast closeCodewordsRel_ncard_le_qpow C y δ

end CodingTheory

#print axioms CodingTheory.closeCodewordsRel_ncard_le_hammingBallVolume
#print axioms CodingTheory.Lambda_le_hammingBallVolume
#print axioms CodingTheory.listDecodable_hammingBallVolume
#print axioms CodingTheory.Lambda_le_qEntropy_card
#print axioms CodingTheory.closeCodewordsRel_ncard_le_qEntropy_card
#print axioms CodingTheory.listDecodable_qEntropy_card
#print axioms CodingTheory.Lambda_le_qEntropy_real_radius_card
#print axioms CodingTheory.closeCodewordsRel_ncard_le_qEntropy_real_radius_card
#print axioms CodingTheory.listDecodable_qEntropy_real_radius_card
#print axioms CodingTheory.one_le_Lambda_of_nonempty
#print axioms CodingTheory.one_le_Lambda_and_Lambda_le_hammingBallVolume
#print axioms CodingTheory.one_le_Lambda_and_Lambda_le_qEntropy_card
#print axioms CodingTheory.one_le_Lambda_and_Lambda_le_qEntropy_real_radius_card
#print axioms CodingTheory.uniqueDecodable_zero
#print axioms CodingTheory.Lambda_le_qpow
#print axioms CodingTheory.one_le_Lambda_and_Lambda_le_qpow
#print axioms CodingTheory.closeCodewordsRel_ncard_le_qpow
#print axioms CodingTheory.listDecodable_qpow
