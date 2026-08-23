/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipBound
import ArkLib.Data.CodingTheory.ProximityGap.SparseDirectionWindow

/-!
# Near-affine foundation for the k = 2 universal law (scratch)

Two lemmas for the near-affine regime:
* `affine_mem_rsCode_two` — an affine word `i ↦ a + b·dom i` is a degree-`< 2`
  codeword (the k = 2 analog of `const_mem_rsCode_one`).
* `residual_two_zero_affine` — a vanishing collinearity residual on `![i,j,c]`
  (with `dom i ≠ dom j`) forces `(dom c, u₁ c)` onto the affine interpolant line
  through the first two graph points: `u₁ c = a + b · dom c`.
-/

open Finset Polynomial

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}

omit [DecidableEq F] in
/-- The affine word `i ↦ a + b·dom i` is a degree-`< 2` Reed–Solomon codeword. -/
theorem affine_mem_rsCode_two (dom : Fin n ↪ F) (a b : F) :
    (fun i : Fin n => a + b * dom i) ∈ (rsCode dom 2 : Submodule F (Fin n → F)) := by
  refine ⟨C a + C b * X, ?_, ?_⟩
  · have h1 : (C a + C b * X).degree ≤ 1 := by
      refine le_trans (degree_add_le _ _) ?_
      refine max_le (le_trans degree_C_le (by norm_num)) ?_
      refine le_trans (degree_mul_le _ _) ?_
      refine le_trans (add_le_add degree_C_le degree_X_le) ?_
      norm_num
    exact lt_of_le_of_lt h1 (by norm_num)
  · funext i
    simp [eval_add, eval_mul, eval_C, eval_X]

omit [DecidableEq F] in
/-- A vanishing `k = 2` residual on `![i,j,c]` with distinct domain points forces
`(dom c, u₁ c)` onto the affine line through `(dom i, u₁ i)` and `(dom j, u₁ j)`. -/
theorem residual_two_zero_affine (dom : Fin n ↪ F) {i j c : Fin n} (u₁ : Fin n → F)
    (hij : dom i ≠ dom j)
    (h : residual dom 2 ![i, j, c] u₁ = 0) :
    u₁ c = (u₁ i - (u₁ j - u₁ i) / (dom j - dom i) * dom i)
         + (u₁ j - u₁ i) / (dom j - dom i) * dom c := by
  -- expand the 3×3 bordered determinant
  have hdet : residual dom 2 ![i, j, c] u₁
      = (dom j - dom i) * u₁ c + (dom i - dom c) * u₁ j + (dom c - dom j) * u₁ i := by
    unfold residual borderedMatrix
    rw [Matrix.det_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue]
    norm_num [pow_zero, pow_one]
    ring
  rw [hdet] at h
  have hne : dom j - dom i ≠ 0 := sub_ne_zero.mpr (Ne.symm hij)
  field_simp
  linear_combination h

end ProximityGap.Ownership

#print axioms ProximityGap.Ownership.affine_mem_rsCode_two
#print axioms ProximityGap.Ownership.residual_two_zero_affine
