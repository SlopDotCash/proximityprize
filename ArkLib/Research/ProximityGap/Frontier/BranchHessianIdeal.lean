/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
-/
import ArkLib.Research.ProximityGap.Frontier.ScalarHessianLocalOrder
import Mathlib.Tactic

/-! # The scalar Hessian belongs to the square of the branch polar ideal

The two coordinates in a parametrization are elements of a differential
coefficient ring. Differentiating the root equation puts the evaluated
scalar partial in the ideal of its two coordinate partials. The entire
scalar Hessian consequently belongs to the square of that same ideal.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.BranchHessianIdeal

variable {A : Type*} [CommRing A] [Differential A]

/-- Evaluate the two coordinates of the equation on a branch. -/
def atPoint (x y : A) : A[X][X] →+* A :=
  (evalRingHom y).comp (mapRingHom (evalRingHom x))

/-- Partial derivative in the coordinate of the inner polynomial ring. -/
def coordinate (F : A[X][X]) : A[X][X] :=
  letI : Differential A[X] := ⟨(Polynomial.derivative' (R := A)).restrictScalars ℤ⟩
  Differential.mapCoeffs F

local instance : Differential A[X] := ⟨Differential.mapCoeffs⟩

/-- Differentiate in the scalar field while holding the two independent
polynomial coordinates constant. -/
def scalar (F : A[X][X]) : A[X][X] := Differential.mapCoeffs F

private theorem at_monomial (x y : A) (n : ℕ) (a : A[X]) :
    atPoint x y (monomial n a) = a.eval x * y^n := by
  simp [atPoint]

private theorem inner_chain (x : A) (a : A[X]) :
    (a.eval x)′ = (Differential.mapCoeffs a).eval x + a.derivative.eval x*x′ := by
  simpa using Differential.deriv_aeval_eq x a

/-- Total scalar derivative of the bivariate equation at two moving coordinates. -/
theorem point_chain (x y : A) (F : A[X][X]) :
    (atPoint x y F)′ =
      atPoint x y (scalar F) + atPoint x y (coordinate F)*x′ + atPoint x y F.derivative*y′ := by
  induction F using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [map_add, scalar, coordinate, derivative_add, add_mul] at *
    rw [ha,hb]
    ring
  | monomial n a =>
    simp only [at_monomial, scalar, coordinate, Differential.mapCoeffs_monomial,
      derivative_monomial, Differential.deriv.leibniz, Differential.deriv.leibniz_pow,
      smul_eq_mul, nsmul_eq_mul, inner_chain]
    change _ = (Differential.mapCoeffs a).eval x*y^n +
      a.derivative.eval x*y^n*x′ + (a*(n : A[X])).eval x*y^(n-1)*y′
    simp only [eval_mul, eval_natCast]
    ring

/-- The scalar partial at a branch root lies in every ideal containing its
two coordinate partials. -/
theorem scalar_mem (x y : A) (F : A[X][X]) (h : atPoint x y F = 0) (I : Ideal A)
    (hx : atPoint x y (coordinate F) ∈ I) (hy : atPoint x y F.derivative ∈ I) :
    atPoint x y (scalar F) ∈ I := by
  have hh := point_chain x y F
  rw [h,map_zero] at hh
  have hm := I.add_mem (I.mul_mem_right x′ hx) (I.mul_mem_right y′ hy)
  have he : atPoint x y (scalar F) =
      -(atPoint x y (coordinate F)*x′ + atPoint x y F.derivative*y′) := by
    linear_combination -hh
  rw [he]
  exact I.neg_mem hm

/-- The proper scalar Hessian at a branch root is in the square of every
ideal containing the evaluated coordinate and value partial derivatives. -/
theorem hessian_mem_square (x y : A) (F : A[X][X]) (h : atPoint x y F = 0) (I : Ideal A)
    (hx : atPoint x y (coordinate F) ∈ I) (hy : atPoint x y F.derivative ∈ I) :
    atPoint x y (ScalarHessianLocalOrder.hessian F) ∈ I^2 := by
  have hz := scalar_mem x y F h I hx hy
  rw [pow_two, ScalarHessianLocalOrder.hessian]
  simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,pow_two]
  apply (I*I).add_mem
  · apply (I*I).sub_mem
    · exact (I*I).mul_mem_left _ (Ideal.mul_mem_mul hy hy)
    · rw [mul_assoc (2*_) _ _]
      exact (I*I).mul_mem_left _ (Ideal.mul_mem_mul hy hz)
  · exact (I*I).mul_mem_left _ (Ideal.mul_mem_mul hz hz)

#print axioms point_chain
#print axioms hessian_mem_square

end ArkLib.ProximityGap.Frontier.BranchHessianIdeal
