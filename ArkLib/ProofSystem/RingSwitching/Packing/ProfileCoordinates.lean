/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.ProfileCoordinates
import ArkLib.ProofSystem.RingSwitching.Packing.FiniteObservation

/-!
# Faithful profile carriers as coordinate families

A profile carrier is additively equivalent to each of its complete coordinate families, so a
finite carrier has `|L| ^ (2 ^ κ)` elements. Its column
family is the packing transposition of its row family, and the coordinates of a finite tensor
observation are the shared weighted observation and its coordinate slices. These statements use
the explicit embeddings `φ₀`, `φ₁` and the profile's inverse laws, without identifying the
ambient algebra action on the carrier with either embedding.

The native orientation is the reverse of upstream PR #1257: rows carry the basis in
the `φ₁` factor, columns in the `φ₀` factor. This adapter preserves the native convention.
-/


namespace RingSwitching.RingSwitchingProfile

open Module

noncomputable section

variable {B L : Type} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
  (P : RingSwitchingProfile B L κ)

/-- Additive equivalence between the carrier and its complete column-coordinate family. -/
def columnEquiv : P.A ≃+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeColumns
  invFun c := ∑ u, P.φ₀ (P.basis u) * P.φ₁ (c u)
  left_inv z := by simpa only [mul_comm] using (P.decomposeColumns_spec z).symm
  right_inv c := by simpa only [mul_comm] using P.decomposeColumns_recompose c
  map_add' x y := funext (P.decomposeColumns_add x y)

/-- Additive equivalence between the carrier and its complete row-coordinate family. -/
def rowEquiv : P.A ≃+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeRows
  invFun c := ∑ v, P.φ₀ (c v) * P.φ₁ (P.basis v)
  left_inv z := (P.decomposeRows_spec z).symm
  right_inv := P.decomposeRows_recompose
  map_add' x y := funext (P.decomposeRows_add x y)

/-- Column coordinates commute with finite sums of carrier elements. -/
theorem decomposeColumns_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeColumns (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeColumns (f i) :=
  map_sum P.columnEquiv f s

/-- Row coordinates commute with finite sums of carrier elements. -/
theorem decomposeRows_sum {ι : Type*} (s : Finset ι) (f : ι → P.A) :
    P.decomposeRows (∑ i ∈ s, f i) = ∑ i ∈ s, P.decomposeRows (f i) :=
  map_sum P.rowEquiv f s

/-- A finite carrier has exactly `|L| ^ (2 ^ κ)` elements. -/
theorem card_A [Fintype L] [Fintype P.A] : Fintype.card P.A = Fintype.card L ^ 2 ^ κ := by
  classical
  rw [Fintype.card_congr P.columnEquiv.toEquiv, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin]

/-- Transposing a carrier's row family gives exactly its column family, for every element. -/
theorem transpose_decomposeRows (z : P.A) :
    (Packing.PackingData.ofBasis P.basis).transpose (P.decomposeRows z) =
      P.decomposeColumns z := by
  conv_rhs => rw [P.decomposeRows_spec z]
  rw [P.decomposeColumns_sum]
  funext u
  change Fin κ → Fin 2 at u
  calc
    _ = ∑ v, P.basis.repr (P.decomposeRows z v) u • P.basis v :=
      (Packing.PackingData.ofBasis P.basis).transpose_apply _ u
    _ = _ := by simp only [P.decomposeColumns_φ₀_mul_φ₁, Finset.sum_apply, Algebra.smul_def]

/-- Reading the column family back recovers the original row family. -/
theorem transpose_symm_decomposeColumns (z : P.A) :
    (Packing.PackingData.ofBasis P.basis).transpose.symm (P.decomposeColumns z) =
      P.decomposeRows z := by
  rw [← P.transpose_decomposeRows]
  exact (Packing.PackingData.ofBasis P.basis).transpose.symm_apply_apply _

/-- Native columns of a finite tensor observation are the shared weighted packing coordinates. -/
theorem decomposeRows_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeRows (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.PackingData.ofBasis P.basis).observe a v := by
  rw [P.decomposeRows_sum]
  funext i
  change (∑ y, P.decomposeRows (P.φ₀ (a y) * P.φ₁ (v y))) i =
    ∑ y, P.basis.repr (v y) i • a y
  simp only [P.decomposeRows_φ₀_mul_φ₁, Finset.sum_apply, Algebra.smul_def, mul_comm]

/-- Native rows of a finite tensor observation are the coordinate slices of its factor families. -/
theorem decomposeColumns_observation {Y : Type*} [Fintype Y] (a v : Y → L) :
    P.decomposeColumns (∑ y, P.φ₀ (a y) * P.φ₁ (v y)) =
      (Packing.PackingData.ofBasis P.basis).coordinateSlices a v := by
  rw [← P.transpose_decomposeRows, P.decomposeRows_observation]
  exact (Packing.PackingData.ofBasis P.basis).transpose_observe a v

end

end RingSwitching.RingSwitchingProfile
