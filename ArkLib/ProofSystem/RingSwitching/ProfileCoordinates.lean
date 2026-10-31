/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Profile
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Inverse laws for the native ring-switching profile

The inverse-coordinate interfaces in upstream ArkLib PR #1257
(`a3351e66943b4f4431c571b91526fdf4abc94ba4`) are consequences of the native
profile's existing additive and atomic laws. Native rows use the left embedding on coordinates
and the right embedding on basis vectors; this is the opposite naming convention to upstream's
new packing profile. No additional profile assumptions are introduced here.
-/

namespace RingSwitching.RingSwitchingProfile

variable {B L : Type*} {κ : ℕ} [CommRing B] [CommRing L] [Algebra B L]
    (P : RingSwitchingProfile B L κ)

/-- Native row coordinates form an additive map. -/
def rowsAddHom : P.A →+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeRows
  map_zero' := by
    ext u
    have h := P.decomposeRows_φ₀_mul_φ₁ 0 0 u
    simpa using h
  map_add' x y := funext (P.decomposeRows_add x y)

/-- Native column coordinates form an additive map. -/
def columnsAddHom : P.A →+ ((Fin κ → Fin 2) → L) where
  toFun := P.decomposeColumns
  map_zero' := by
    ext u
    have h := P.decomposeColumns_φ₀_mul_φ₁ 0 0 u
    simpa using h
  map_add' x y := funext (P.decomposeColumns_add x y)

/-- Reconstructing an arbitrary row tuple and reading it back preserves the tuple. -/
theorem decomposeRows_recompose (c : (Fin κ → Fin 2) → L) :
    P.decomposeRows (∑ u, P.φ₀ (c u) * P.φ₁ (P.basis u)) = c := by
  change P.rowsAddHom _ = c
  rw [map_sum]
  ext u
  simp [rowsAddHom, Finset.sum_apply, P.decomposeRows_φ₀_mul_φ₁]

/-- Reconstructing an arbitrary column tuple and reading it back preserves the tuple. -/
theorem decomposeColumns_recompose (c : (Fin κ → Fin 2) → L) :
    P.decomposeColumns (∑ u, P.φ₁ (c u) * P.φ₀ (P.basis u)) = c := by
  rw [show (∑ u, P.φ₁ (c u) * P.φ₀ (P.basis u)) =
      ∑ u, P.φ₀ (P.basis u) * P.φ₁ (c u) from
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
  change P.columnsAddHom _ = c
  rw [map_sum]
  ext u
  simp [columnsAddHom, Finset.sum_apply, P.decomposeColumns_φ₀_mul_φ₁]

/-- Row coordinates characterize their reconstruction. -/
theorem decomposeRows_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeRows z = c ↔ z = ∑ u, P.φ₀ (c u) * P.φ₁ (P.basis u) := by
  constructor
  · intro h
    simpa only [h] using P.decomposeRows_spec z
  · rintro rfl
    exact P.decomposeRows_recompose c

/-- Column coordinates characterize their reconstruction. -/
theorem decomposeColumns_eq_iff (z : P.A) (c : (Fin κ → Fin 2) → L) :
    P.decomposeColumns z = c ↔ z = ∑ u, P.φ₁ (c u) * P.φ₀ (P.basis u) := by
  constructor
  · intro h
    simpa only [h] using P.decomposeColumns_spec z
  · rintro rfl
    exact P.decomposeColumns_recompose c

/-- Reconstruction makes the row-coordinate map injective. -/
theorem decomposeRows_injective : Function.Injective P.decomposeRows := by
  intro x y h
  rw [P.decomposeRows_spec x, h, ← P.decomposeRows_spec y]

/-- The native atomic laws force the two embeddings to agree on the base ring. -/
theorem embeddings_agree (b : B) :
    P.φ₀ (algebraMap B L b) = P.φ₁ (algebraMap B L b) := by
  apply P.decomposeRows_injective
  ext u
  have h₀ := P.decomposeRows_φ₀_mul_φ₁ (algebraMap B L b) 1 u
  have h₁ := P.decomposeRows_φ₀_mul_φ₁ 1 (algebraMap B L b) u
  simp only [map_one, mul_one, one_mul] at h₀ h₁
  rw [h₀, h₁]
  simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]

end RingSwitching.RingSwitchingProfile
