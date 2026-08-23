/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Z-affine decomposition — a surface affine in the inner variable splits

A bivariate `w : F[Z][X]` whose coefficients all have `Z`-degree at most `1` is a single
affine pencil: there are `A₀ A₁ : F[X]` with `natDegree ≤ natDegree w` such that every
inner specialization satisfies `w.map (evalRingHom z) = A₀ + z·A₁`.

This is the bridge from the global surface factor (affine in `Z` by fiber-linearity) to
the explicit affine pair consumed by the capture machinery.
-/

namespace Polynomial

variable {F : Type*} [CommSemiring F]

/-- The `j`-th inner-coefficient extraction of a bivariate polynomial, as a polynomial in
the outer variable. -/
noncomputable def innerCoeff (w : F[X][X]) (j : ℕ) : F[X] :=
  ∑ i ∈ w.support, Polynomial.monomial i ((w.coeff i).coeff j)

theorem innerCoeff_coeff (w : F[X][X]) (j i : ℕ) :
    (innerCoeff w j).coeff i = (w.coeff i).coeff j := by
  classical
  rw [innerCoeff, Polynomial.finset_sum_coeff]
  by_cases hi : i ∈ w.support
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hb
      rw [Polynomial.coeff_monomial, if_neg hb]
    · intro habs
      exact absurd hi habs
  · rw [Finset.sum_eq_zero, Polynomial.notMem_support_iff.mp hi, Polynomial.coeff_zero]
    intro b hb
    rw [Polynomial.coeff_monomial, if_neg]
    intro hbi
    rw [hbi] at hb
    exact hi hb

theorem innerCoeff_natDegree_le (w : F[X][X]) (j : ℕ) :
    (innerCoeff w j).natDegree ≤ w.natDegree := by
  classical
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  refine le_trans (Polynomial.natDegree_monomial_le _) ?_
  exact Polynomial.le_natDegree_of_mem_supp i hi

/-- **The Z-affine decomposition.**  A surface whose coefficients are `Z`-affine
specializes everywhere to the pencil of its two inner-coefficient extractions. -/
theorem map_evalRingHom_eq_affine {w : F[X][X]}
    (haff : ∀ i, (w.coeff i).natDegree ≤ 1) (z : F) :
    w.map (Polynomial.evalRingHom z)
      = innerCoeff w 0 + Polynomial.C z * innerCoeff w 1 := by
  classical
  ext i
  rw [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, innerCoeff_coeff, innerCoeff_coeff]
  -- `eval z` of a degree-`≤ 1` polynomial is `c₀ + z·c₁`
  have h := haff i
  conv_lhs => rw [Polynomial.eval_eq_sum_range'
    (show (w.coeff i).natDegree < 2 from lt_of_le_of_lt h Nat.one_lt_two)]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  ring

end Polynomial

/-! ## Axiom audit -/
#print axioms Polynomial.innerCoeff_coeff
#print axioms Polynomial.innerCoeff_natDegree_le
#print axioms Polynomial.map_evalRingHom_eq_affine
