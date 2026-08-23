/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode
import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# Reed–Solomon generalized-Singleton list-decoding code-size bound

Combines the Reed–Solomon list-size bound `ReedSolomon.reedSolomon_Lambda_le` (`Λ(RS, δ) ≤ dZ`)
with the generic ST20 generalized-Singleton theorem
`CodingTheory.linear_C_le_generalized_singleton_st20`, discharging the latter's `Λ`-hypothesis for
`RS[k]` via the Sudan/Guruswami–Sudan machinery.
-/

namespace ReedSolomon

open scoped Polynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Reed–Solomon generalized-Singleton list-decoding bound.**  With the `Λ`-input discharged by
`reedSolomon_Lambda_le`, the ST20 generalized-Singleton theorem gives the concrete code-cardinality
bound for `RS[k]`: `|RS| ≤ |F|^(n − ⌊((dZ+1)/dZ)·δ·n⌋)`. -/
theorem reedSolomon_C_le_generalized_singleton
    {k dX dZ : ℕ} [NeZero k] {α : ι ↪ F} {δ : ℝ}
    (hℓ_pos : 0 < dZ) (hℓ_lt : dZ < Fintype.card F)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (hlat : δ * (Fintype.card ι : ℝ) = (⌊δ * (Fintype.card ι : ℝ)⌋₊ : ℝ))
    (ha_le : ⌊((dZ : ℝ) + 1) / dZ * δ * Fintype.card ι⌋₊ ≤ Fintype.card ι)
    (hbig : Fintype.card ι < (dX + 1) * (dZ + 1))
    (he : ⌊δ * Fintype.card ι⌋₊ < Fintype.card ι)
    (hdeg : dX + dZ * (k - 1) < Fintype.card ι - ⌊δ * Fintype.card ι⌋₊) :
    (Set.ncard ((ReedSolomon.code α k : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((dZ : ℝ) + 1) / dZ * δ * Fintype.card ι) : ℝ)) :=
  CodingTheory.linear_C_le_generalized_singleton_st20 (ReedSolomon.code α k) dZ δ
    hℓ_pos hℓ_lt hδ_pos hδ_lt hlat ha_le
    (reedSolomon_Lambda_le (α := α) (k := k) (dX := dX) (dZ := dZ) (le_of_lt hδ_pos) hbig he hdeg)

end ReedSolomon
