/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Adapted-basis transport for GK16 Claim 16

The structural-transport residual `GK16Claim16StructuralData` (in
`ArkLib/Data/CodingTheory/SubspaceDesign.lean`) asks, per coordinate, for an *invertible
recombination* `Q` of a fixed basis `P` of the underlying polynomial space `U` together
with a `dim W`-element index set `T` whose members lie in a prescribed subspace
`W ≤ U` (the per-coordinate orbit-vanishing subspace). This file proves the purely
linear-algebraic engine behind that data:

* `exists_adapted_basis` — for a finite-dimensional space, a fixed basis `bU : Basis (Fin n)`
  and any subspace `W` of `finrank d`, there is a second basis `bQ : Basis (Fin n)` whose
  members on a `d`-element index set `T` all lie in `W`.
* `exists_adapted_recombination` — the same data expressed through the change-of-basis
  matrix `c := (bU.toMatrix bQ)ᵀ`, which is **invertible** (`det c ≠ 0`) and satisfies the
  recombination identity `bQ l = ∑ m, c l m • bU m`. This is exactly the shape the
  Claim-16 engine `claim16_rootMultiplicity_ge` consumes.

Everything here is `sorry`/axiom-clean.
-/

open Matrix Module

namespace ArkLib.FRS.GK16

variable {F : Type*} [Field F] {M : Type*} [AddCommGroup M] [Module F M]

/-- **Adapted basis existence.** Let `U` be a finite-dimensional `F`-space with a basis
`bU : Basis (Fin n) F U` (so `finrank U = n`), and let `W ≤ U` be a subspace with
`finrank W = d`. Then there is a basis `bQ : Basis (Fin n) F U` and a `d`-element index
set `T ⊆ Fin n` such that every `bQ l` for `l ∈ T` lies in `W`.

Construction: pick a complement `W'` of `W` in `U` (`Submodule.exists_isCompl`), splice a
basis of `W` (indexed `Fin d`) and a basis of `W'` (indexed `Fin (n - d)`) through
`Submodule.prodEquivOfIsCompl`, and reindex `Fin d ⊕ Fin (n - d) ≃ Fin n` so that the
`W`-vectors occupy the first `d` indices `T := Finset.image castLE univ`. -/
theorem exists_adapted_basis {n d : ℕ} [Module.Finite F M]
    (bU : Basis (Fin n) F M) (W : Submodule F M) (hW : Module.finrank F W = d) :
    ∃ (bQ : Basis (Fin n) F M) (T : Finset (Fin n)),
      T.card = d ∧ (∀ l ∈ T, (bQ l) ∈ W) := by
  classical
  -- A complement `W'` of `W`.
  obtain ⟨W', hWW'⟩ := W.exists_isCompl
  -- Dimensions: `finrank W' = n - d`, and `d + (n - d) = n` since `d ≤ n`.
  have hn : Module.finrank F M = n := by
    simpa using bU.repr.finrank_eq.trans (by simp)
  have hd_le : d ≤ n := by
    rw [← hn, ← hW]; exact W.finrank_le
  have hW' : Module.finrank F W' = n - d := by
    have hsum : Module.finrank F W + Module.finrank F W' = Module.finrank F M :=
      Submodule.finrank_add_eq_of_isCompl hWW'
    omega
  -- Bases of `W` and `W'`.
  let bW : Basis (Fin d) F W := by
    rw [← hW]; exact Module.finBasis F W
  let bW' : Basis (Fin (n - d)) F W' := by
    rw [← hW']; exact Module.finBasis F W'
  -- Splice through the complement iso `(W × W') ≃ₗ M`.
  let bProd : Basis (Fin d ⊕ Fin (n - d)) F M :=
    (bW.prod bW').map (Submodule.prodEquivOfIsCompl W W' hWW')
  -- Reindex `Fin d ⊕ Fin (n - d) ≃ Fin (d + (n - d)) = Fin n`.
  have hdn : d + (n - d) = n := by omega
  let e : Fin d ⊕ Fin (n - d) ≃ Fin n :=
    (finSumFinEquiv).trans (finCongr hdn)
  refine ⟨bProd.reindex e, Finset.image (e ∘ Sum.inl) Finset.univ, ?_, ?_⟩
  · -- Card of the image of the (injective) `e ∘ Sum.inl` over `Fin d`.
    rw [Finset.card_image_of_injective _ (e.injective.comp Sum.inl_injective)]
    simp
  · -- Members at those indices are the `W`-basis vectors, hence in `W`.
    intro l hl
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    simp only [Basis.reindex_apply, Function.comp_apply, Equiv.symm_apply_apply]
    -- `bProd (Sum.inl j) = prodEquivOfIsCompl (bW.prod bW' (Sum.inl j))`; its first
    -- component is `bW j ∈ W`, its second is `0`, so the sum lies in `W`.
    show bProd (Sum.inl j) ∈ W
    have hfst : (bW.prod bW' (Sum.inl j)).1 = bW j := Basis.prod_apply_inl_fst _ _ j
    have hsnd : (bW.prod bW' (Sum.inl j)).2 = 0 := Basis.prod_apply_inl_snd _ _ j
    have hval : bProd (Sum.inl j)
        = ((bW.prod bW' (Sum.inl j)).1 : M) + ((bW.prod bW' (Sum.inl j)).2 : M) := by
      simp only [bProd, Basis.map_apply]
      exact Submodule.coe_prodEquivOfIsCompl' W W' hWW' (bW.prod bW' (Sum.inl j))
    rw [hval, hfst, hsnd, ZeroMemClass.coe_zero, add_zero]
    exact (bW j).2

/-- **Adapted recombination (Claim-16 shape).** From a basis `bU : Basis (Fin n) F M` and a
subspace `W` of `finrank d`, produce a *recombination* of the family `P := ⇑bU` adapted to
`W`: a family `Q : Fin n → M`, a coefficient matrix `c : Fin n → Fin n → F` with
`(Matrix.of c).det ≠ 0` and `Q l = ∑ m, c l m • P m`, plus a `d`-element index set `T`
whose `Q`-members lie in `W`.

This is exactly the per-coordinate data the GK16 Claim-16 engine
(`claim16_rootMultiplicity_ge`) consumes (with `P` the polynomial family, `W` the
orbit-vanishing subspace, and `T` indexing the `dim A_i`-dimensional vanishing part).

`c := (bU.toMatrix bQ)ᵀ`: invertible since `bU.toMatrix bQ` is the change-of-basis matrix
between two bases (`Basis.invertibleToMatrix`), and `det cᵀ = det c`. The recombination
identity is `Basis.sum_toMatrix_smul_self`. -/
theorem exists_adapted_recombination {n d : ℕ} [Module.Finite F M]
    (bU : Basis (Fin n) F M) (W : Submodule F M) (hW : Module.finrank F W = d) :
    ∃ (Q : Fin n → M) (c : Fin n → Fin n → F) (T : Finset (Fin n)),
      (Matrix.of c).det ≠ 0 ∧
      (∀ l, Q l = ∑ m, c l m • bU m) ∧
      T.card = d ∧
      (∀ l ∈ T, Q l ∈ W) := by
  classical
  obtain ⟨bQ, T, hT_card, hT_mem⟩ := exists_adapted_basis bU W hW
  refine ⟨⇑bQ, (bU.toMatrix ⇑bQ)ᵀ, T, ?_, ?_, hT_card, hT_mem⟩
  · -- `det cᵀ = det c ≠ 0`, since `bU.toMatrix bQ` is invertible.
    have hinv : Invertible (bU.toMatrix ⇑bQ) := bU.invertibleToMatrix bQ
    have hunit : IsUnit (bU.toMatrix ⇑bQ).det := isUnit_det_of_invertible _
    show ((bU.toMatrix ⇑bQ)ᵀ).det ≠ 0
    rw [Matrix.det_transpose]
    exact hunit.ne_zero
  · -- Recombination identity `bQ l = ∑ m, (bU.toMatrix bQ) m l • bU m`.
    intro l
    rw [← bU.sum_toMatrix_smul_self ⇑bQ l]
    rfl

end ArkLib.FRS.GK16
