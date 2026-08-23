/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Spartan.Basic

/-!
# Degree bounds for the Spartan sum-check virtual polynomials (issue #114)

To instantiate the sum-check oracle reductions on Spartan's virtual polynomials, the polynomials
must inhabit the sum-check oracle-statement type `R⦃≤ deg⦄[X Fin n]`. This module proves the
required degree bounds:

* `toMLE_evalC_mem_restrictDegree` — fixing the row variables of `Matrix.toMLE` at a point (via `C`)
  leaves a polynomial that is multilinear (degree ≤ 1) in the column variables. The engine is
  `toMLE_evalC_eq_sum`, the explicit `C`-scaled column-MLE decomposition of the partial evaluation.
* `secondSCVP_mem_restrictDegree` — the second sum-check virtual polynomial `ℳ(Y)` has degree ≤ 2
  in each variable (a product of two multilinear factors).
-/

open MvPolynomial Matrix

namespace Spartan

variable {R : Type} [CommRing R]

/-- Fixing the `eqPolynomial` row variables at `r_x` via `C` commutes with `C` of the base-ring
evaluation. -/
theorem eqPoly_evalC_eq_C_eval {m n : ℕ} (xBits : Fin m → Fin 2) (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x)
        (eqPolynomial (fun i => ((xBits i : Fin 2) : MvPolynomial (Fin n) R)))
      = C (eval r_x (eqPolynomial (fun i => ((xBits i : Fin 2) : R)))) := by
  classical
  simp only [eqPolynomial, map_prod, singleEqPolynomial, Function.comp_apply, map_add, map_mul,
    map_sub, map_one, eval_X, map_natCast]

/-- **Polynomial-level partial evaluation of `Matrix.toMLE`.** Fixing the row variables at `r_x`
yields the explicit `C`-scaled combination of the column MLEs. -/
theorem toMLE_evalC_eq_sum {m n : ℕ} (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE
      = ∑ xBits : Fin m → Fin 2,
          C (eval r_x (eqPolynomial (fun i => ((xBits i : Fin 2) : R)))) *
            MLE' (M (finFunctionFinEquiv xBits)) := by
  classical
  show eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) (MLE ((MLE' ∘ M) ∘ finFunctionFinEquiv)) = _
  rw [MLE, map_sum]
  refine Finset.sum_congr rfl fun xBits _ => ?_
  rw [eval_mul, eval_C, eqPoly_evalC_eq_C_eval]; rfl

/-- **The row-fixed matrix MLE is multilinear in the column variables (degree ≤ 1).** -/
theorem toMLE_evalC_mem_restrictDegree {m n : ℕ} (M : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R)
    (r_x : Fin m → R) :
    eval ((C : R →+* MvPolynomial (Fin n) R) ∘ r_x) M.toMLE ∈ R⦃≤ 1⦄[X Fin n] := by
  classical
  rw [toMLE_evalC_eq_sum, mem_restrictDegree_iff_degreeOf_le]
  intro j
  refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le fun xBits _ => ?_)
  refine le_trans (degreeOf_mul_le j _ _) ?_
  rw [degreeOf_C]
  have h1 : degreeOf j (MLE' (M (finFunctionFinEquiv xBits))) ≤ 1 :=
    (mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j
  omega

variable [IsDomain R] [Fintype R] (pp : Spartan.PublicParams)

open Spartan.Spec

omit [IsDomain R] [Fintype R] in
/-- **Degree bound of the second sum-check virtual polynomial** (`≤ 2` per variable): packages
`ℳ(Y)` for the sum-check oracle statement `R⦃≤ 2⦄[X Fin ℓ_n]`. -/
theorem secondSCVP_mem_restrictDegree
    (stmt : Statement.AfterLinearCombination R pp)
    (oStmt : ∀ i, OracleStatement.AfterLinearCombination R pp i) :
    secondSumCheckVirtualPolynomial R pp stmt oStmt ∈ R⦃≤ 2⦄[X Fin pp.ℓ_n] := by
  classical
  rw [mem_restrictDegree_iff_degreeOf_le]
  intro j
  have hM : ∀ idx : R1CS.MatrixIdx,
      degreeOf j (eval (fun i => (C : R →+* MvPolynomial (Fin pp.ℓ_n) R) (stmt.2.1 i))
        (oStmt (.inr (.inl idx))).toMLE) ≤ 1 :=
    fun idx => (mem_restrictDegree_iff_degreeOf_le _ _).mp
      (toMLE_evalC_mem_restrictDegree _ stmt.2.1) j
  simp only [secondSumCheckVirtualPolynomial, Function.comp_def, Fin.cast_eq_self]
  refine le_trans (degreeOf_add_le j _ _)
    (max_le (le_trans (degreeOf_add_le j _ _) (max_le ?_ ?_)) ?_)
  · refine le_trans (degreeOf_mul_le j _ _)
      (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .A))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)
  · refine le_trans (degreeOf_mul_le j _ _)
      (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .B))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)
  · refine le_trans (degreeOf_mul_le j _ _)
      (le_trans (add_le_add (degreeOf_mul_le j _ _) le_rfl) ?_)
    rw [degreeOf_C]
    exact Nat.add_le_add (Nat.add_le_add (le_refl 0) (hM .C))
      ((mem_restrictDegree_iff_degreeOf_le _ _).mp (MLE_mem_restrictDegree _) j)

#print axioms toMLE_evalC_mem_restrictDegree
#print axioms secondSCVP_mem_restrictDegree

end Spartan
