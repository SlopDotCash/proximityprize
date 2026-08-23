/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeMatrixEquidist
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Joint equidistribution from linearly independent messages (GLMRSW22 second moment)

`RandomLinearCodeMatrixEquidist.lean` proved joint equidistribution of `G ↦ M * G` from a
**right inverse** `M * N = 1`. This file supplies that right inverse from the natural hypothesis —
**linear independence of the message rows** of `M` (full row rank over the field `F`) — and packages
the resulting joint uniformity.

For two linearly independent messages `m, m'` (a rank-2 block `M = ![m, m']`), this gives the
**pairwise uniformity** `(m ᵥ* G, m' ᵥ* G) ~ Uniform((ι → F)²)`, the GLMRSW22 / ABF26 T3.11
second-moment input (issue #79).

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `exists_rightInverse_of_linearIndependent_rows` — full row rank ⟹ a right inverse `M * N = 1`.
* `map_mul_uniform_of_linearIndependent_rows` — joint codewords of linearly independent messages
  are uniform on `Matrix (Fin r) ι F`.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- A matrix whose rows are linearly independent (full row rank) has a right inverse `M * N = 1`. -/
theorem exists_rightInverse_of_linearIndependent_rows
    {M : Matrix (Fin r) (Fin k) F} (h : LinearIndependent F M.row) :
    ∃ N : Matrix (Fin k) (Fin r) F, M * N = 1 := by
  rw [← Matrix.mulVec_surjective_iff_exists_right_inverse]
  have hsurj : Function.Surjective M.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    show Matrix.rank M = Module.finrank F (Fin r → F)
    rw [h.rank_matrix, Module.finrank_fintype_fun_eq_card]
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, by rw [← Matrix.mulVecLin_apply]; exact hx⟩

/-- **Joint equidistribution from linear independence.** If the message rows of `M` are linearly
independent, the uniform generator-matrix law pushes forward under `G ↦ M * G` to the uniform law
on `Matrix (Fin r) ι F`. The `r = 2` case is the pairwise uniformity feeding the GLMRSW22 second
moment. -/
theorem map_mul_uniform_of_linearIndependent_rows
    {M : Matrix (Fin r) (Fin k) F} (h : LinearIndependent F M.row) :
    (PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)
      = PMF.uniformOfFintype (Matrix (Fin r) ι F) := by
  obtain ⟨N, hN⟩ := exists_rightInverse_of_linearIndependent_rows h
  exact map_mul_uniformOfFintype hN

end ArkLib.RandomLinearCode

-- Axiom audit.
#print axioms ArkLib.RandomLinearCode.exists_rightInverse_of_linearIndependent_rows
#print axioms ArkLib.RandomLinearCode.map_mul_uniform_of_linearIndependent_rows
