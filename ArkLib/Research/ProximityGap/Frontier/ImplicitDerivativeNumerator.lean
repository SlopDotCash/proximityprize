/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Polynomial numerators for repeated implicit differentiation

The identity is division-free and holds at a root even when the value derivative
vanishes there. The coefficient derivation fixes the scalar parameter.
-/

set_option autoImplicit false
noncomputable section

open Polynomial
open scoped Differential

namespace ArkLib.ProximityGap.Frontier.ImplicitDerivativeNumerator

variable {A B : Type*} [CommRing A] [Differential A] [CommRing B] [Differential B]
    [Algebra A B] [DifferentialAlgebra A B]

/-- Tangential differentiation multiplied by the value derivative of the equation. -/
def along (f p : A[X]) : A[X] :=
  f.derivative * Differential.mapCoeffs p - Differential.mapCoeffs f * p.derivative

/-- `numerator f j` represents derivative order `j+1` with denominator
`(f.derivative)^(2*j+1)`. -/
def numerator (f : A[X]) : ℕ → A[X]
  | 0 => -Differential.mapCoeffs f
  | j+1 => f.derivative * along f (numerator f j) -
      (2*j+1 : ℕ) * numerator f j * along f f.derivative

theorem along_aeval (f p : A[X]) (y : B) (hy : aeval y f = 0) :
    aeval y (along f p) = aeval y f.derivative * (aeval y p)′ := by
  have hroot := Differential.deriv_aeval_eq y f
  rw [hy, map_zero] at hroot
  simp only [along, map_sub, map_mul, Differential.deriv_aeval_eq]
  linear_combination -(aeval y p.derivative) * hroot.symm

/-- Repeated quotient rule as a polynomial identity on the entire root section.
No separability or unit condition is needed in this direction. -/
theorem numerator_aeval (f : A[X]) (y : B) (hy : aeval y f = 0) (j : ℕ) :
    aeval y (numerator f j) = aeval y f.derivative ^ (2*j+1) *
      (Differential.deriv^[j+1]) y := by
  induction j with
  | zero =>
      have hh := Differential.deriv_aeval_eq y f
      rw [hy, map_zero] at hh
      simp only [numerator, map_neg, Nat.mul_zero, Nat.zero_add, pow_one,
        Function.iterate_one]
      linear_combination -hh.symm
  | succ j ih =>
      let h := aeval y f.derivative
      let u := (Differential.deriv^[j+1]) y
      have hstep : (Differential.deriv^[j+1+1]) y = u′ := by
        exact Function.iterate_succ_apply' _ _ _
      simp only [numerator, map_sub, map_mul, map_natCast, along_aeval f _ y hy, ih, hstep]
      change h * (h * (h^(2*j+1)*u)′) -
          ((2*j+1 : ℕ) : B) * (h^(2*j+1)*u) * (h*h′) =
          h^(2*(j+1)+1)*u′
      rw [Differential.deriv.leibniz, Differential.deriv.leibniz_pow]
      simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
      rw [show 2*(j+1)+1 = 2*j+1+2 by omega, pow_add, pow_succ]
      ring

/-- A root whose coordinate derivative of order `j+1` vanishes supplies a common
root of the original equation and the polynomial numerator. -/
theorem numerator_aeval_zero (f : A[X]) (y : B) (hy : aeval y f = 0) (j : ℕ)
    (hd : (Differential.deriv^[j+1]) y = 0) : aeval y (numerator f j) = 0 := by
  rw [numerator_aeval _ _ hy, hd, mul_zero]

/-- Every polynomial witness of degree at most d satisfies the order-(d+1)
numerator, including witnesses passing through singular points. -/
theorem polynomial_witness {R : Type*} [CommRing R]
    [Differential R[X]] [Algebra A R[X]] [DifferentialAlgebra A R[X]]
    (hdiff : ∀ q : R[X], q′ = q.derivative) (f : A[X]) (q : R[X])
    (hroot : aeval q f = 0) (d : ℕ) (hdeg : q.natDegree ≤ d) :
    aeval q (numerator f d) = 0 := by
  apply numerator_aeval_zero f q hroot
  have heq : (fun z : R[X] => z′) = Polynomial.derivative := funext hdiff
  change ((fun z : R[X] => z′)^[d+1]) q = 0
  rw [heq]
  exact iterate_derivative_eq_zero (Nat.lt_succ_of_le hdeg)

end ArkLib.ProximityGap.Frontier.ImplicitDerivativeNumerator

#print axioms ArkLib.ProximityGap.Frontier.ImplicitDerivativeNumerator.numerator_aeval
#print axioms ArkLib.ProximityGap.Frontier.ImplicitDerivativeNumerator.numerator_aeval_zero

open ArkLib.ProximityGap.Frontier.ImplicitDerivativeNumerator in
#print axioms polynomial_witness
