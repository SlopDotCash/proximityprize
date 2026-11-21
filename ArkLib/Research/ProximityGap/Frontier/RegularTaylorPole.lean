/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Derivative
import ArkLib.Data.Polynomial.Differential.RationalTaylor
import Mathlib.Tactic

/-! # A genuine first-order polynomial solution with a long Taylor denominator

Over the rational function field F(T), the equation (X+T)P' = DP has a
degree-D solution whose first two Taylor coordinates are T and D at zero.
The top coefficient has denominator T^(D-1) in lowest terms, even though
the equation and both initial coordinates are polynomial in the challenge.
-/

set_option autoImplicit false
noncomputable section
namespace ProximityGap.RegularTaylorPole
open Polynomial
variable {F : Type*} [Field F]

/-- A polynomial solution of degree d+1 with an integral initial jet. -/
def witness (F : Type*) [Field F] (d : ℕ) : Polynomial (RatFunc F) :=
  C ((RatFunc.X ^ d)⁻¹) * (X + C RatFunc.X)^(d+1)

/-- The equation holds identically in the coordinate X. -/
theorem equation (d : ℕ) :
    (X+C RatFunc.X)*(witness F d).derivative = (d+1 : Polynomial (RatFunc F))*witness F d := by
  simp only [witness,derivative_C_mul,derivative_pow_succ,derivative_X_add_C,mul_one]
  rw [pow_succ, map_add, map_natCast, map_one]
  ring

/-- Both entries of the regular initial jet belong to F[T], including when
the degree of the candidate grows. The separant is T. -/
theorem initial_jet (d : ℕ) :
    (witness F d).eval 0 = RatFunc.X ∧ ((witness F d).derivative.eval 0) = (d+1 : RatFunc F) := by
  have ht : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · simp [witness,pow_succ,ht]
  · rw [witness,derivative_C_mul,derivative_pow_succ,derivative_X_add_C,mul_one]
    simp
    field_simp

/-- The candidate has degree exactly d+1 and leading coefficient 1/T^d. -/
theorem top_coefficient (d : ℕ) :
    (witness F d).natDegree = d+1 ∧
      (witness F d).coeff (d+1) = ((RatFunc.X : RatFunc F)^d)⁻¹ := by
  have ht : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  simp [witness,coeff_X_add_C_pow,ht,natDegree_C_mul]

/-- Exactly d powers of the separant are needed for the top Taylor coordinate
to extend polynomially in the challenge. The lower bound holds over every field. -/
theorem polynomial_numerator_iff (d τ : ℕ) :
    (∃ N : F[X], algebraMap F[X] (RatFunc F) N =
      RatFunc.X^τ * (witness F d).coeff (d+1)) ↔ d ≤ τ := by
  rw [(top_coefficient (F:=F) d).2]
  have ht : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  constructor
  · rintro ⟨N,h⟩
    by_contra! hsmall
    obtain ⟨s,hs⟩ := Nat.exists_eq_add_of_lt hsmall
    have hprod : algebraMap F[X] (RatFunc F) (N*X^(s+1)) = 1 := by
      rw [map_mul,map_pow,RatFunc.algebraMap_X,h,hs]
      rw [show τ+s+1 = τ+(s+1) by omega, pow_add]
      field_simp
    have hpol : N*X^(s+1) = 1 := RatFunc.algebraMap_injective F (by simpa using hprod)
    have := congrArg (eval (0:F)) hpol
    simp at this
  · intro h
    obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨X^s,?_⟩
    simp [pow_add]
    field_simp

open PolynomialDifferential

/-- The equation with challenge T as an element of the campaign's differential
polynomial ring. -/
def jetEquation (F : Type*) [Field F] (d : ℕ) : DifferentialPolynomial (RatFunc F) 1 :=
  (MvPolynomial.X none + MvPolynomial.C RatFunc.X)*MvPolynomial.X (some 1) -
    MvPolynomial.C (d+1 : RatFunc F)*MvPolynomial.X (some 0)

/-- The polynomial solves the differential equation used by the formal Taylor chart. -/
theorem differential_root (d : ℕ) :
    differentialSpecialization (jetEquation F d) (witness F d) = 0 := by
  unfold differentialSpecialization jetEquation differentialSpecializationHom
  simp [equation]

/-- The separant at the origin is the indeterminate itself, independently of
the selected jet. -/
theorem chart_separant (d : ℕ) (jet : Fin 2 → RatFunc F) :
    jetEvaluation (separant (jetEquation F d) (Fin.last 1)) 0 jet = RatFunc.X := by
  simp [jetEquation,separant,jetEvaluation,MvPolynomial.pderiv_X]

/-- In the actual rational Taylor chart the same if-and-only-if holds
whenever the ordinary characteristic pivots through degree d+1 are nonzero. -/
theorem chart_numerator_iff (d τ : ℕ)
    (hchar : ringChar F = 0 ∨ d+1 < ringChar F) :
    (∃ N : F[X], algebraMap F[X] (RatFunc F) N = RatFunc.X^τ *
      rationalTaylorCoefficient 0 (jetEquation F d) (polynomialJet 0 (witness F d)) (d+1)) ↔ d ≤ τ := by
  have hpivot (i : ℕ) (hi : 1 < i) (hid : i ≤ d+1) : (i : RatFunc F) ≠ 0 := by
    have hf : (i : F) ≠ 0 := natCast_ne_zero_of_ringChar_eq_zero_or_lt hchar (by omega) hid
    simpa using (RatFunc.C_injective (K:=F)).ne hf
  have h := rationalTaylorCoefficient_eq_solution 0 (jetEquation F d) (witness F d)
    (differential_root d) (by rw [chart_separant]; exact RatFunc.X_ne_zero) (d+1) (by simpa using hpivot)
  simpa [h] using polynomial_numerator_iff (F:=F) d τ

#print axioms chart_numerator_iff
#print axioms equation
#print axioms initial_jet
#print axioms top_coefficient
#print axioms polynomial_numerator_iff
end ProximityGap.RegularTaylorPole
