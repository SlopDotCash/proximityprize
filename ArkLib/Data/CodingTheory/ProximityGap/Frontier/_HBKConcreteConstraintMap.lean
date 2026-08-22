/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKClearedDerivativeRecurrence

/-!
# The concrete HBK constraint map

For derivative order `m` and representative `u`, HBK's residual constraint polynomial is

`P_{m,u} = Σ_{a,b,c} λ_{a,b,c} u^{-h(b+c)} R_{m,a,b,c}`.

Its degree is `< A+D` for `a<A`, `m<D`; hence extracting coefficients `0,…,A+D-1` gives a finite
linear map of exactly the shape counted by the kernel theorem.  Kernel membership forces every
`P_{m,u}` to vanish identically. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKConcreteConstraintMap

open scoped BigOperators
open Polynomial
open HBKSpecialCoefficientKernel HBKClearedDerivativeRecurrence

variable {F : Type*} [Field F] [DecidableEq F]

/-- HBK's residual constraint polynomial `P_{m,u}`. -/
noncomputable def constraintPolynomial
    (h A B : ℕ) (coeffs : CoeffSpace F A B) (m : ℕ) (u : F) : F[X] :=
  ∑ p : Fin A × Fin B × Fin B,
    C (coeffs p * u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ)))) *
      residualPolynomial h p.1 p.2.1 p.2.2 m

/-- The concrete finite HBK constraint map, extracting all coefficients below `A+D`. -/
noncomputable def constraintMap (h A B D : ℕ) (U : Finset F) :
    CoeffSpace F A B →ₗ[F] ConstraintSpace F A D U where
  toFun coeffs q :=
    (constraintPolynomial h A B coeffs q.1 q.2.2).coeff q.2.1
  map_add' x y := by
    classical
    funext q
    simp [constraintPolynomial, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    classical
    funext q
    simp [constraintPolynomial, mul_assoc, Finset.mul_sum]

/-- Each constraint polynomial has degree `<A+D` in the indexed range `m<D`. -/
theorem natDegree_constraintPolynomial_lt
    {h A B D : ℕ} (coeffs : CoeffSpace F A B) {m : ℕ} (hm : m < D) (u : F) :
    (constraintPolynomial h A B coeffs m u).natDegree < A + D := by
  classical
  unfold constraintPolynomial
  have hsum :
      (∑ p : Fin A × Fin B × Fin B,
        C (coeffs p * u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ)))) *
          residualPolynomial h p.1 p.2.1 p.2.2 m : F[X]).natDegree ≤ A + D - 1 :=
    natDegree_sum_le_of_forall_le (s := Finset.univ) (n := A + D - 1)
      (fun p : Fin A × Fin B × Fin B =>
        C (coeffs p * u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ)))) *
          residualPolynomial h p.1 p.2.1 p.2.2 m) (by
        intro p _
        calc
          (C (coeffs p * u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ)))) *
              residualPolynomial h p.1 p.2.1 p.2.2 m : F[X]).natDegree
            ≤ (C (coeffs p * u⁻¹ ^ (h * ((p.2.1 : ℕ) + (p.2.2 : ℕ)))) : F[X]).natDegree +
                (residualPolynomial h p.1 p.2.1 p.2.2 m).natDegree := natDegree_mul_le
          _ ≤ 0 + (p.1 : ℕ) + m := by
            rw [natDegree_C]
            simpa using natDegree_residualPolynomial_le (F := F) h p.1 p.2.1 p.2.2 m
          _ ≤ A + D - 1 := by have := p.1.isLt; omega)
  exact hsum.trans_lt (by omega)

/-- Vanishing of every extracted coordinate forces every indexed residual polynomial to be zero. -/
theorem constraintPolynomial_eq_zero_of_mem_ker
    {h A B D : ℕ} {U : Finset F} {coeffs : CoeffSpace F A B}
    (hker : constraintMap h A B D U coeffs = 0)
    {m : ℕ} (hm : m < D) {u : F} (hu : u ∈ U) :
    constraintPolynomial h A B coeffs m u = 0 := by
  classical
  apply Polynomial.ext
  intro r
  by_cases hr : r < A + D
  · let q : Fin D × Fin (A + D) × U :=
      (⟨m, hm⟩, ⟨r, hr⟩, ⟨u, hu⟩)
    have hq := congrFun hker q
    simpa [constraintMap, q] using hq
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le (natDegree_constraintPolynomial_lt coeffs hm u) (by omega))

end ArkLib.ProximityGap.Frontier.HBKConcreteConstraintMap

#print axioms ArkLib.ProximityGap.Frontier.HBKConcreteConstraintMap.natDegree_constraintPolynomial_lt
#print axioms ArkLib.ProximityGap.Frontier.HBKConcreteConstraintMap.constraintPolynomial_eq_zero_of_mem_ker
