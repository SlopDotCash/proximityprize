/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HBKSpecializationNonzero

/-!
# HBK cleared-derivative recurrence

Multiplying the ordinary derivative by `X(X-1)` preserves the factors
`X^{hb}(X-1)^{hc}`.  The residual polynomial obeys a simple linear recurrence and gains at most
one degree per derivative.  These residuals are the `P_{m,a,b,c}` used in the concrete HBK
constraint map. Issue #466.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.HBKClearedDerivativeRecurrence

open Polynomial

variable {F : Type*} [Field F]

/-- The derivative operator used by HBK after clearing the nonzero factors `x(x-1)`. -/
noncomputable def clearedDerivative (P : F[X]) : F[X] := X * (X - 1) * P.derivative

/-- Residual polynomial after `m` cleared derivatives of
`X^a X^{hb}(X-1)^{hc}`. -/
noncomputable def residualPolynomial (h a b c : ℕ) : ℕ → F[X]
  | 0 => (X : F[X]) ^ a
  | m + 1 =>
      (X : F[X]) * (X - 1) * (residualPolynomial h a b c m).derivative +
        C (h * b : F) * (X - 1) * residualPolynomial h a b c m +
        C (h * c : F) * X * residualPolynomial h a b c m

@[simp] theorem residualPolynomial_zero (h a b c : ℕ) :
    residualPolynomial (F := F) h a b c 0 = X ^ a := rfl

@[simp] theorem residualPolynomial_succ (h a b c m : ℕ) :
    residualPolynomial (F := F) h a b c (m + 1) =
      X * (X - 1) * (residualPolynomial h a b c m).derivative +
        C (h * b : F) * (X - 1) * residualPolynomial h a b c m +
        C (h * c : F) * X * residualPolynomial h a b c m := rfl

private theorem X_mul_derivative_X_pow (n : ℕ) :
    (X : F[X]) * ((X : F[X]) ^ n).derivative = C (n : F) * X ^ n := by
  obtain rfl | n := n
  · simp
  · rw [Polynomial.derivative_X_pow]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Nat.succ_sub_one]
    ring

private theorem X_sub_one_mul_derivative_pow (n : ℕ) :
    ((X : F[X]) - 1) * (((X : F[X]) - 1) ^ n).derivative =
      C (n : F) * (X - 1) ^ n := by
  obtain rfl | n := n
  · simp
  · rw [Polynomial.derivative_pow]
    simp
    ring

/-- One cleared derivative preserves the two large power factors and applies the residual
recurrence. -/
theorem clearedDerivative_mul_power_factors (h a b c m : ℕ) :
    clearedDerivative
      (residualPolynomial (F := F) h a b c m * X ^ (h * b) * (X - 1) ^ (h * c)) =
      residualPolynomial h a b c (m + 1) * X ^ (h * b) * (X - 1) ^ (h * c) := by
  let P := residualPolynomial (F := F) h a b c m
  rw [clearedDerivative, Polynomial.derivative_mul, Polynomial.derivative_mul]
  change (X : F[X]) * (X - 1) *
      ((P.derivative * X ^ (h * b) + P * (X ^ (h * b)).derivative) *
          (X - 1) ^ (h * c) +
        P * X ^ (h * b) * ((((X : F[X]) - 1) ^ (h * c)).derivative)) = _
  calc
    _ = (X * (X - 1) * P.derivative) * X ^ (h * b) * (X - 1) ^ (h * c) +
        P * (X - 1) * (X * (X ^ (h * b)).derivative) * (X - 1) ^ (h * c) +
        P * X ^ (h * b) * X *
          (((X : F[X]) - 1) * (((X : F[X]) - 1) ^ (h * c)).derivative) := by ring
    _ = (X * (X - 1) * P.derivative) * X ^ (h * b) * (X - 1) ^ (h * c) +
        P * (X - 1) * (C (h * b : F) * X ^ (h * b)) * (X - 1) ^ (h * c) +
        P * X ^ (h * b) * X * (C (h * c : F) * (X - 1) ^ (h * c)) := by
          rw [X_mul_derivative_X_pow, X_sub_one_mul_derivative_pow]
          simp only [Nat.cast_mul]
    _ = residualPolynomial h a b c (m + 1) * X ^ (h * b) *
        (X - 1) ^ (h * c) := by
          rw [residualPolynomial_succ]
          dsimp [P]
          ring

/-- Iterating the cleared derivative gives the residual recurrence exactly. -/
theorem iterate_clearedDerivative_monomial (h a b c m : ℕ) :
    (clearedDerivative^[m])
      (X ^ a * X ^ (h * b) * (X - 1) ^ (h * c) : F[X]) =
      residualPolynomial h a b c m * X ^ (h * b) * (X - 1) ^ (h * c) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      exact clearedDerivative_mul_power_factors h a b c m

/-- The residual polynomial has degree at most `a+m`, exactly the `A+D` coefficient budget. -/
theorem natDegree_residualPolynomial_le (h a b c m : ℕ) :
    (residualPolynomial (F := F) h a b c m).natDegree ≤ a + m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [residualPolynomial_succ]
      let P := residualPolynomial (F := F) h a b c m
      have hPbound : P.natDegree ≤ a + m := ih
      have hXm1 : ((X : F[X]) - 1).natDegree = 1 := by
        simpa only [C_1] using natDegree_X_sub_C (1 : F)
      have hd : P.derivative.natDegree ≤ P.natDegree - 1 := natDegree_derivative_le P
      have hXX : (X * (X - 1) : F[X]).natDegree ≤ 2 := by
        calc
          _ ≤ (X : F[X]).natDegree + (X - 1 : F[X]).natDegree := natDegree_mul_le
          _ = 2 := by rw [natDegree_X, hXm1]
      have hfirst : (X * (X - 1) * P.derivative).natDegree ≤ a + (m + 1) := by
        by_cases hp : P.derivative = 0
        · simp [hp]
        · have hpdeg : 0 < P.natDegree := by
            by_contra h
            have hz : P.natDegree = 0 := by omega
            exact hp (derivative_of_natDegree_zero hz)
          calc
            _ ≤ (X * (X - 1) : F[X]).natDegree + P.derivative.natDegree :=
              natDegree_mul_le
            _ ≤ 2 + (P.natDegree - 1) := Nat.add_le_add hXX hd
            _ ≤ a + (m + 1) := by omega
      have hsecond :
          (C (h * b : F) * (X - 1) * P).natDegree ≤ a + (m + 1) := by
        have hCX : (C (h * b : F) * (X - 1) : F[X]).natDegree ≤ 1 := by
          calc
            _ ≤ (C (h * b : F)).natDegree + (X - 1 : F[X]).natDegree := natDegree_mul_le
            _ = 1 := by rw [natDegree_C, hXm1, zero_add]
        calc
          _ ≤ (C (h * b : F) * (X - 1) : F[X]).natDegree + P.natDegree :=
            natDegree_mul_le
          _ ≤ 1 + P.natDegree := Nat.add_le_add_right hCX _
          _ ≤ a + (m + 1) := by omega
      have hthird : (C (h * c : F) * X * P).natDegree ≤ a + (m + 1) := by
        have hCX : (C (h * c : F) * X : F[X]).natDegree ≤ 1 := by
          calc
            _ ≤ (C (h * c : F)).natDegree + (X : F[X]).natDegree := natDegree_mul_le
            _ = 1 := by rw [natDegree_C, natDegree_X, zero_add]
        calc
          _ ≤ (C (h * c : F) * X : F[X]).natDegree + P.natDegree := natDegree_mul_le
          _ ≤ 1 + P.natDegree := Nat.add_le_add_right hCX _
          _ ≤ a + (m + 1) := by omega
      exact (natDegree_add_le _ _).trans (max_le
        ((natDegree_add_le _ _).trans (max_le hfirst hsecond)) hthird)

end ArkLib.ProximityGap.Frontier.HBKClearedDerivativeRecurrence

#print axioms ArkLib.ProximityGap.Frontier.HBKClearedDerivativeRecurrence.clearedDerivative_mul_power_factors
#print axioms ArkLib.ProximityGap.Frontier.HBKClearedDerivativeRecurrence.iterate_clearedDerivative_monomial
#print axioms ArkLib.ProximityGap.Frontier.HBKClearedDerivativeRecurrence.natDegree_residualPolynomial_le
