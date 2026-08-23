/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode
import ArkLib.ProofSystem.Stir.OutOfDomSmpl

/-!
# STIR out-of-domain sampling for Reed–Solomon (unconditional)

STIR's Lemma 4.5.1 (`OutOfDomSmpl.out_of_dom_smpl_1`) bounds the list-decoding collision probability
*given* a list-decodability hypothesis `listDecodable C δ ℓ`.  Discharging that hypothesis for `RS`
via the Sudan/Guruswami–Sudan bound `ReedSolomon.reedSolomon_listDecodable` (with `ℓ = dZ`) makes the
STIR bound **unconditional** for Reed–Solomon under the Sudan parameters.
-/

namespace ReedSolomon

open scoped Polynomial NNReal
open ListDecodable

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **STIR out-of-domain sampling for Reed–Solomon (Lemma 4.5.1, unconditional).**  The list-size
input `ℓ = dZ` is supplied by `reedSolomon_listDecodable`, so STIR's collision-probability bound
holds unconditionally for `RS[degree]` under the Sudan conditions. -/
theorem reedSolomon_out_of_dom_smpl_1
    {δ : ℝ≥0} {s dX dZ degree : ℕ} [NeZero degree] {f : ι → F} {φ : ι ↪ F}
    (h_nonempty : Nonempty (OutOfDomSmpl.domainComplement φ))
    (hbig : Fintype.card ι < (dX + 1) * (dZ + 1))
    (he : ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι)
    (hdeg : dX + dZ * (degree - 1) < Fintype.card ι - ⌊(δ : ℝ) * Fintype.card ι⌋₊) :
    OutOfDomSmpl.listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
      (((dZ : ℝ≥0) * ((dZ : ℝ≥0) - 1) / 2))
        * (((degree : ℝ≥0) - 1) / (Fintype.card F - Fintype.card ι)) ^ s :=
  OutOfDomSmpl.out_of_dom_smpl_1 (l := (dZ : ℝ≥0)) ((ReedSolomon.code φ degree : Set (ι → F))) rfl
    (show listDecodable ((ReedSolomon.code φ degree : Set (ι → F))) (δ : ℝ) ((dZ : ℝ≥0) : ℝ) by
      rw [NNReal.coe_natCast]
      exact reedSolomon_listDecodable (α := φ) (k := degree) (dX := dX) (dZ := dZ)
        δ.coe_nonneg hbig he hdeg)
    h_nonempty

/-- **STIR out-of-domain sampling for Reed–Solomon (Lemma 4.5.1, simplified form, unconditional).**
The `(l²/2)·(degree/(q−n))^s` variant `out_of_dom_smpl_2`, made unconditional for `RS[degree]` via
`reedSolomon_listDecodable`. -/
theorem reedSolomon_out_of_dom_smpl_2
    {δ : ℝ≥0} {s dX dZ degree : ℕ} [NeZero degree] {f : ι → F} {φ : ι ↪ F}
    (h_nonempty : Nonempty (OutOfDomSmpl.domainComplement φ))
    (hbig : Fintype.card ι < (dX + 1) * (dZ + 1))
    (he : ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι)
    (hdeg : dX + dZ * (degree - 1) < Fintype.card ι - ⌊(δ : ℝ) * Fintype.card ι⌋₊) :
    OutOfDomSmpl.listDecodingCollisionProbability φ f δ s degree h_nonempty ≤
      (((dZ : ℝ≥0) ^ 2 / 2))
        * (((degree : ℝ≥0)) / (Fintype.card F - Fintype.card ι)) ^ s :=
  OutOfDomSmpl.out_of_dom_smpl_2 (l := (dZ : ℝ≥0)) ((ReedSolomon.code φ degree : Set (ι → F))) rfl
    (show listDecodable ((ReedSolomon.code φ degree : Set (ι → F))) (δ : ℝ) ((dZ : ℝ≥0) : ℝ) by
      rw [NNReal.coe_natCast]
      exact reedSolomon_listDecodable (α := φ) (k := degree) (dX := dX) (dZ := dZ)
        δ.coe_nonneg hbig he hdeg)
    h_nonempty

/-- **The smooth-domain Reed–Solomon code is `(δ, dZ)`-list-decodable.**  `smoothCode φ m` is by
definition `RS[2^m]` over the smooth domain `φ`, so the Sudan/GS list-decodability bound applies
directly.  This is the list-decodability hypothesis WHIR's out-of-domain-sampling lemmas consume. -/
theorem smoothCode_listDecodable {m dX dZ : ℕ} {φ : ι ↪ F} [Smooth φ] {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hbig : Fintype.card ι < (dX + 1) * (dZ + 1))
    (he : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hdeg : dX + dZ * (2 ^ m - 1) < Fintype.card ι - ⌊δ * Fintype.card ι⌋₊) :
    ListDecodable.listDecodable ((ReedSolomon.smoothCode φ m : Set (ι → F))) δ (dZ : ℝ) := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  exact reedSolomon_listDecodable (α := φ) (k := 2 ^ m) (dX := dX) (dZ := dZ) hδ0 hbig he hdeg

end ReedSolomon
