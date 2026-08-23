/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Invertible row-submatrix from injectivity (#371, WB-pencil infrastructure)

A rectangular matrix over a field whose kernel is trivial has an invertible square
row-submatrix.  This is the pencil programme's anchor: the far direction's
Welch–Berlekamp matrix is injective, the selected rows give the determinant whose
top coefficient survives along the γ-pencil, and the bad-scalar count is its root
count.  Generic linear algebra; a candidate for `ToMathlib`.
-/

open Matrix

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [DecidableEq F]

/-- **Invertible row selection.**  If `M : Matrix (Fin n) α F` has trivial
kernel, some `card α` rows form an invertible square matrix. -/
theorem exists_invertible_row_submatrix {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix (Fin n) α F) (hinj : ∀ v, M.mulVec v = 0 → v = 0) :
    ∃ I : α → Fin n, Function.Injective I ∧ (M.submatrix I id).det ≠ 0 := by
  classical
  -- the row space is everything: column rank = m by injectivity, row rank = column rank
  have hinj' : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact hinj v hv
  have hrank : M.rank = Fintype.card α := by
    have hker : LinearMap.ker M.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hinj'
    have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hker, finrank_bot, add_zero] at h1
    have h2 : Module.finrank F (α → F) = Fintype.card α := by simp
    show Module.finrank F (LinearMap.range M.mulVecLin) = Fintype.card α
    exact h1.trans h2
  have hrowspan : Submodule.span F (Set.range M) = ⊤ := by
    have ht := Matrix.rank_transpose M
    rw [hrank] at ht
    have hrange : LinearMap.range Mᵀ.mulVecLin = Submodule.span F (Set.range M) := by
      rw [Matrix.range_mulVecLin]
      have hcol : Mᵀ.col = M := rfl
      rw [hcol]
    have hr : Mᵀ.rank = Module.finrank F (Submodule.span F (Set.range M)) := by
      show Module.finrank F (LinearMap.range Mᵀ.mulVecLin) = _
      rw [hrange]
    rw [hr] at ht
    have hfull : Module.finrank F (α → F) = Fintype.card α := by simp
    exact Submodule.eq_top_of_finrank_eq (by rw [ht, hfull])
  -- extract an independent spanning subset of the rows
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent F (Set.range M)
  rw [hrowspan] at hbspan
  -- b is a basis; it has exactly m elements
  haveI : Fintype b := Set.Finite.fintype
    (Set.Finite.subset (Set.finite_range M) hbsub)
  have hbcard : Fintype.card b = Fintype.card α := by
    have hb : ⊤ ≤ Submodule.span F (Set.range ((↑) : b → (α → F))) := by
      rw [Subtype.range_coe, hbspan]
    have hbasis : Module.finrank F (α → F) = Fintype.card b :=
      Module.finrank_eq_card_basis (Module.Basis.mk hbind hb)
    have h2 : Module.finrank F (α → F) = Fintype.card α := by simp
    omega
  -- choose row indices realizing b
  have hchoice : ∀ x : b, ∃ i : Fin n, M i = (x : α → F) := fun x => hbsub x.2
  choose f hf using hchoice
  have hfinj : Function.Injective f := by
    intro x y hxy
    have : (x : α → F) = y := by rw [← hf x, ← hf y, hxy]
    exact Subtype.ext this
  -- enumerate b by Fin m
  have hequiv : Nonempty (α ≃ b) := by
    rw [← Fintype.card_eq]
    simp [hbcard]
  obtain ⟨e⟩ := hequiv
  refine ⟨f ∘ e, hfinj.comp e.injective, ?_⟩
  -- the selected rows are independent, so the determinant is nonzero
  intro hdet
  have hdetT : (M.submatrix (f ∘ e) id)ᵀ.det = 0 := by
    rw [Matrix.det_transpose]
    exact hdet
  obtain ⟨v, hv0, hvker⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdetT
  -- mulVec of the transpose = row combination
  have hrowdep : ∑ j : α, v j • M (f (e j)) = 0 := by
    funext c
    have := congrFun hvker c
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.submatrix_apply, Function.comp_apply, id_eq] at this
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using this
  -- contradicts independence of b
  have hrowdep' : ∑ j : α, v j • ((e j : b) : α → F) = 0 := by
    have hM : ∀ j : α, M (f (e j)) = ((e j : b) : α → F) := fun j => hf (e j)
    calc ∑ j : α, v j • ((e j : b) : α → F)
        = ∑ j : α, v j • M (f (e j)) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hM j]
      _ = 0 := hrowdep
  have hsum : ∑ x : b, v (e.symm x) • (x : α → F) = 0 := by
    rw [← Equiv.sum_comp e (fun x : b => v (e.symm x) • (x : α → F))]
    simpa using hrowdep'
  have hzero := Fintype.linearIndependent_iff.mp hbind
    (fun x : b => v (e.symm x)) hsum
  apply hv0
  funext j
  have := hzero (e j)
  simpa using this

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.exists_invertible_row_submatrix
