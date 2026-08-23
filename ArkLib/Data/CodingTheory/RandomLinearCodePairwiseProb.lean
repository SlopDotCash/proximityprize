/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RandomLinearCodeRankEquidist
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Field.Basic

/-!
# GLMRSW22 pairwise joint hit probability (the second-moment summand)

Composing the joint equidistribution from linear independence
(`map_mul_uniform_of_linearIndependent_rows`) with the uniform set probability, this gives the
**second-moment summand** of the GLMRSW22 random-linear-code argument (issue #79): for a rank-2
message block `M` (two linearly independent messages `M 0`, `M 1`), the random codewords land
jointly in a target set `S` with probability `(|S| / qⁿ)²`.

## Main results (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `mul_uniform_mem_prob_of_linearIndependent_rows` — set probability from linear independence.
* `pairwise_joint_mem_prob` — `Pr[M 0 ᵥ* G ∈ S ∧ M 1 ᵥ* G ∈ S] = (|S| / qⁿ)²`.
-/

namespace ArkLib.RandomLinearCode

open scoped Matrix ENNReal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {k r : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Set probability from linear independence of the message block (one step). -/
theorem mul_uniform_mem_prob_of_linearIndependent_rows
    {M : Matrix (Fin r) (Fin k) F} (h : LinearIndependent F M.row)
    (S : Set (Matrix (Fin r) ι F)) [Fintype S] :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)).toOuterMeasure S
      = Fintype.card S / Fintype.card (Matrix (Fin r) ι F) := by
  rw [map_mul_uniform_of_linearIndependent_rows h, PMF.toOuterMeasure_uniformOfFintype_apply]

/-- **The second-moment summand.** For a rank-2 message block `M` (rows `M 0`, `M 1` linearly
independent), the random codewords land jointly in a finite target set `S` with probability
`(|S| / qⁿ)²` — the per-pair term the GLMRSW22 second moment sums over independent message pairs. -/
theorem pairwise_joint_mem_prob {M : Matrix (Fin 2) (Fin k) F}
    (h : LinearIndependent F M.row) (S : Finset (ι → F)) :
    ((PMF.uniformOfFintype (Matrix (Fin k) ι F)).map (fun G => M * G)).toOuterMeasure
        {D : Matrix (Fin 2) ι F | D 0 ∈ S ∧ D 1 ∈ S}
      = ((Fintype.card S : ℝ≥0∞) / Fintype.card (ι → F)) ^ 2 := by
  classical
  have hcardEvent :
      Fintype.card {D : Matrix (Fin 2) ι F // D 0 ∈ S ∧ D 1 ∈ S} = (Fintype.card S) ^ 2 := by
    have e : {D : Matrix (Fin 2) ι F // D 0 ∈ S ∧ D 1 ∈ S} ≃ (↑S × ↑S : Type _) :=
      { toFun := fun D => (⟨D.1 0, D.2.1⟩, ⟨D.1 1, D.2.2⟩)
        invFun := fun p => ⟨![p.1.1, p.2.1], ⟨by simp [p.1.2], by simp [p.2.2]⟩⟩
        left_inv := by rintro ⟨D, hD⟩; apply Subtype.ext; funext i; fin_cases i <;> rfl
        right_inv := by rintro ⟨a, b⟩; rfl }
    rw [Fintype.card_congr e, Fintype.card_prod, ← sq]
  have hcardMat : Fintype.card (Matrix (Fin 2) ι F) = (Fintype.card (ι → F)) ^ 2 := by
    show Fintype.card (Fin 2 → (ι → F)) = (Fintype.card (ι → F)) ^ 2
    rw [Fintype.card_fun, Fintype.card_fin]
  rw [mul_uniform_mem_prob_of_linearIndependent_rows h
        {D : Matrix (Fin 2) ι F | D 0 ∈ S ∧ D 1 ∈ S}]
  have hA : (Fintype.card (↑{D : Matrix (Fin 2) ι F | D 0 ∈ S ∧ D 1 ∈ S}) : ℝ≥0∞)
      = (Fintype.card S : ℝ≥0∞) ^ 2 := by exact_mod_cast hcardEvent
  have hB : (Fintype.card (Matrix (Fin 2) ι F) : ℝ≥0∞) = (Fintype.card (ι → F) : ℝ≥0∞) ^ 2 := by
    exact_mod_cast hcardMat
  rw [hA, hB, div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

end ArkLib.RandomLinearCode

-- Axiom audit.
#print axioms ArkLib.RandomLinearCode.mul_uniform_mem_prob_of_linearIndependent_rows
#print axioms ArkLib.RandomLinearCode.pairwise_joint_mem_prob
