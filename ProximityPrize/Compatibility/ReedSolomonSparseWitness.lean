/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# Sparse polynomial witnesses for Reed–Solomon codewords

The degree argument stays symbolic so callers can instantiate large exponents without
normalizing a concrete polynomial representation in the kernel.
-/

namespace ReedSolomon

open Polynomial

/-- A monomial plus a constant gives a codeword whenever its exponent is below the dimension.
Prove the polynomial witness with symbolic exponents before specializing large parameters. -/
lemma mem_code_monomial_add_constant {F ι : Type*} [Field F]
    (domain : ι ↪ F) {e k : ℕ} (he : e < k) (c : F) :
    (fun i => domain i ^ e + c) ∈ code domain k := by
  refine mem_code_of_polynomial_of_natDegree_lt_of_eval
    ((Polynomial.X : F[X]) ^ e + Polynomial.C c) ?_ ?_
  · exact ((Polynomial.natDegree_add_le _ _).trans (max_le
      (Polynomial.natDegree_X_pow_le _) (by simp))).trans_lt he
  · intro i
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C]

/-- The sum of two monomials gives a codeword when both exponents are below the dimension. -/
lemma mem_code_add_monomials {F ι : Type*} [Field F]
    (domain : ι ↪ F) {e d k : ℕ} (he : e < k) (hd : d < k) :
    (fun i => domain i ^ e + domain i ^ d) ∈ code domain k := by
  refine mem_code_of_polynomial_of_natDegree_lt_of_eval
    ((Polynomial.X : F[X]) ^ e + Polynomial.X ^ d) ?_ ?_
  · exact (Polynomial.natDegree_add_le _ _).trans_lt
      (max_lt (lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) he)
        (lt_of_le_of_lt (Polynomial.natDegree_X_pow_le _) hd))
  · intro i
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]

end ReedSolomon

#print axioms ReedSolomon.mem_code_monomial_add_constant
#print axioms ReedSolomon.mem_code_add_monomials
