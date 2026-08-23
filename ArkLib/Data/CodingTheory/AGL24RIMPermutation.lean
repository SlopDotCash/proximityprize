/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ReducedIntersectionMatrix
import ArkLib.Data.CodingTheory.AGL24Types

/-!
# [AGL24] §3 rung 1: RIM permutation covariance (issue #346, brick 12)

The other half of the type-ordering WLOG: permuting the edge family permutes the reduced
intersection matrix's rows **and** relabels its variables — so the evaluated kernel condition
transports between `(e ∘ σ, α)` and `(e, α ∘ σ⁻¹)`:

* `rimRowEquiv` — the row correspondence `RIMRowIdx (e ∘ σ) ≃ RIMRowIdx e`;
* `RIM_eval_comp_perm` — the entrywise covariance: the row of the permuted instance at
  evaluation `α` equals the corresponding row of the original at evaluation `α ∘ σ⁻¹`;
* `rankDeficit_comp_perm_iff` — **the event transport**: the evaluated kernel-witness event
  of the permuted instance at `α` is the original's at `α ∘ σ⁻¹`. Under any
  permutation-invariant evaluation distribution this gives equality of the per-hypergraph
  failure probabilities across a symmetry class — Remark 2.9 in probability form, the step
  that will divide the certificate count by the class sizes.
-/

open Finset

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The row correspondence of the permuted instance: `(i, j) ↦ (σ i, j)` (the non-minimal
vertex data is definitionally shared since `(e ∘ σ) i = e (σ i)`). -/
def rimRowEquiv {t : ℕ} (e : ι → Finset (Fin (t + 1))) (σ : Equiv.Perm ι) :
    RIMRowIdx (e ∘ σ) ≃ RIMRowIdx e where
  toFun r := ⟨σ r.1, r.2⟩
  invFun r := ⟨σ.symm r.1, ⟨r.2.val, by
    constructor
    · show r.2.val ∈ e (σ (σ.symm r.1))
      rw [Equiv.apply_symm_apply]
      exact r.2.property.1
    · obtain ⟨j', hj'mem, hj'lt⟩ := r.2.property.2
      refine ⟨j', ?_, hj'lt⟩
      show j' ∈ e (σ (σ.symm r.1))
      rw [Equiv.apply_symm_apply]
      exact hj'mem⟩⟩
  left_inv r := by
    obtain ⟨i, j⟩ := r
    refine Sigma.ext (Equiv.symm_apply_apply σ i) ?_
    rw [Subtype.heq_iff_coe_eq (fun x => by simp [Function.comp, Equiv.symm_apply_apply])]
  right_inv r := by
    obtain ⟨i, j⟩ := r
    refine Sigma.ext (Equiv.apply_symm_apply σ i) ?_
    rw [Subtype.heq_iff_coe_eq (fun x => by simp [Function.comp, Equiv.apply_symm_apply])]

/-- **Entrywise covariance**: the evaluated permuted-instance row equals the evaluated
original row at the permuted evaluation. -/
theorem RIM_eval_comp_perm {t k : ℕ} (e : ι → Finset (Fin (t + 1))) (σ : Equiv.Perm ι)
    (α : ι → F) (r : RIMRowIdx (e ∘ σ)) (c : Fin t × Fin k) :
    (MvPolynomial.eval α) (RIM F (e ∘ σ) r c)
      = (MvPolynomial.eval (α ∘ σ.symm)) (RIM F e (rimRowEquiv e σ r) c) := by
  obtain ⟨i, j⟩ := r
  unfold RIM rimRowEquiv
  simp only [Equiv.coe_fn_mk]
  -- The min-terms coincide definitionally ((e ∘ σ) i = e (σ i)); the variable evaluations
  -- coincide through the permutation.
  by_cases h1 : c.1.castSucc = ((e ∘ σ) i).min' ⟨j.val, j.property.1⟩
  · rw [if_pos h1, if_pos (show c.1.castSucc = (e (σ i)).min' _ from h1)]
    rw [map_pow, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_X]
    simp [Function.comp, Equiv.symm_apply_apply]
  · rw [if_neg h1, if_neg (show ¬ c.1.castSucc = (e (σ i)).min' _ from h1)]
    by_cases h2 : c.1.castSucc = j.val
    · rw [if_pos h2, if_pos h2]
      rw [map_neg, map_neg, map_pow, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_X]
      simp [Function.comp, Equiv.symm_apply_apply]
    · rw [if_neg h2, if_neg h2, map_zero, map_zero]

/-- **The event transport** (Remark 2.9, deterministic form): the permuted instance's
evaluated kernel-witness event at `α` is the original's at `α ∘ σ⁻¹`. -/
theorem rankDeficit_comp_perm_iff {t k : ℕ} (e : ι → Finset (Fin (t + 1)))
    (σ : Equiv.Perm ι) (α : ι → F) :
    (∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F (e ∘ σ)).map (MvPolynomial.eval α)).mulVec v = 0)
      ↔ (∃ v : Fin t × Fin k → F, v ≠ 0 ∧
        ((RIM F e).map (MvPolynomial.eval (α ∘ σ.symm))).mulVec v = 0) := by
  have hrow : ∀ (v : Fin t × Fin k → F),
      ((RIM F (e ∘ σ)).map (MvPolynomial.eval α)).mulVec v = 0
        ↔ ((RIM F e).map (MvPolynomial.eval (α ∘ σ.symm))).mulVec v = 0 := by
    intro v
    constructor <;> intro h <;> funext r
    · -- Original row r = permuted row (rimRowEquiv⁻¹ r).
      have := congrFun h ((rimRowEquiv e σ).symm r)
      rw [show (0 : RIMRowIdx e → F) r = 0 from rfl]
      rw [show (0 : RIMRowIdx (e ∘ σ) → F) ((rimRowEquiv e σ).symm r) = 0 from rfl] at this
      rw [← this]
      unfold Matrix.mulVec dotProduct
      refine Finset.sum_congr rfl fun c _ => ?_
      show ((RIM F e).map (MvPolynomial.eval (α ∘ σ.symm))) r c * v c
        = ((RIM F (e ∘ σ)).map (MvPolynomial.eval α)) ((rimRowEquiv e σ).symm r) c * v c
      rw [Matrix.map_apply, Matrix.map_apply]
      rw [RIM_eval_comp_perm e σ α ((rimRowEquiv e σ).symm r) c]
      rw [Equiv.apply_symm_apply]
    · -- Permuted row r = original row (rimRowEquiv r).
      have := congrFun h ((rimRowEquiv e σ) r)
      rw [show (0 : RIMRowIdx (e ∘ σ) → F) r = 0 from rfl]
      rw [show (0 : RIMRowIdx e → F) ((rimRowEquiv e σ) r) = 0 from rfl] at this
      rw [← this]
      unfold Matrix.mulVec dotProduct
      refine Finset.sum_congr rfl fun c _ => ?_
      show ((RIM F (e ∘ σ)).map (MvPolynomial.eval α)) r c * v c
        = ((RIM F e).map (MvPolynomial.eval (α ∘ σ.symm))) ((rimRowEquiv e σ) r) c * v c
      rw [Matrix.map_apply, Matrix.map_apply]
      rw [RIM_eval_comp_perm e σ α r c]
  exact exists_congr fun v => and_congr_right fun _ => hrow v

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.RIM_eval_comp_perm
#print axioms AGL24.rankDeficit_comp_perm_iff
