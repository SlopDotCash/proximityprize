/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import ArkLib.Data.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Clearing denominators in a bivariate substitution

We define `clearDenomY W e P`, which clears denominators for the substitution `Y ↦ W * Y` in a
bivariate polynomial `P : F[X][Y]` using total exponent `e`. The lemma `evalEval_clearDenomY`
gives its evaluation in terms of `P`, and `evalEval_clearDenomY_eq_zero_of_evalEval_eq_zero`
transfers vanishing of `P` to the cleared polynomial.
-/

open Polynomial
open scoped BigOperators Polynomial.Bivariate

namespace Polynomial

variable {F : Type} [Field F]

/-- Clear denominators for the substitution `Y ↦ W * Y`, using total exponent `e`. -/
noncomputable def clearDenomY (W : F[X]) (e : ℕ) (P : F[X][Y]) : F[X][Y] :=
  ∑ i ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (P.coeff i * W ^ (e - i)) * Polynomial.X ^ i

lemma evalEval_clearDenomY (W : F[X]) {e : ℕ} {P : F[X][Y]}
    (he : P.natDegree ≤ e) (z y : F) :
    Polynomial.evalEval z (W.eval z * y) (clearDenomY W e P) =
      (W.eval z) ^ e * Polynomial.evalEval z y P := by
  classical
  have hEvalP : Polynomial.evalEval z y P =
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval z * y ^ i := by
    rw [Polynomial.evalEval]
    rw [show Polynomial.eval (Polynomial.C y) P =
        ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (Polynomial.C y) ^ i by
      exact Polynomial.eval_eq_sum_range (x := Polynomial.C y)]
    simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C]
  rw [clearDenomY]
  simp only [Polynomial.evalEval_finset_sum, Polynomial.evalEval_mul, Polynomial.evalEval_C,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.evalEval_pow, Polynomial.evalEval_X]
  rw [hEvalP, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_le : i ≤ e := by
    have : i < P.natDegree + 1 := Finset.mem_range.mp hi
    omega
  have hid : e - i + i = e := by omega
  rw [mul_pow]
  calc
    Polynomial.eval z (P.coeff i) * Polynomial.eval z W ^ (e - i) *
        (Polynomial.eval z W ^ i * y ^ i)
        = Polynomial.eval z (P.coeff i) *
            ((Polynomial.eval z W ^ (e - i) * Polynomial.eval z W ^ i) * y ^ i) := by ring
    _ = Polynomial.eval z (P.coeff i) * (Polynomial.eval z W ^ e * y ^ i) := by
      rw [← pow_add, hid]
    _ = Polynomial.eval z W ^ e * (Polynomial.eval z (P.coeff i) * y ^ i) := by ring

lemma evalEval_clearDenomY_eq_zero_of_evalEval_eq_zero (W : F[X])
    {e : ℕ} {P : F[X][Y]} (he : P.natDegree ≤ e) {z y : F}
    (hroot : Polynomial.evalEval z y P = 0) :
    Polynomial.evalEval z (W.eval z * y) (clearDenomY W e P) = 0 := by
  rw [evalEval_clearDenomY W he z y, hroot, mul_zero]

end Polynomial
