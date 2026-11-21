/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Inverse Taylor expansion in a differential field

If the coordinate has derivative one and the order-`d+1` derivative of a
given element vanishes, its shifted Taylor polynomial of order `d` evaluates
to that element and every coefficient is a differential constant. The factorials
are invertible when `d` is strictly below the prime characteristic.
-/

set_option autoImplicit false
noncomputable section

open Polynomial Finset
open scoped Differential BigOperators

namespace ArkLib.ProximityGap.Frontier.InverseTaylorFlat

variable {L : Type*} [Field L] [Differential L]

/-- The divided coordinate derivative used in a Taylor coefficient. -/
def dividedDerivative (y : L) (i : ℕ) : L := (Differential.deriv^[i]) y / i.factorial

/-- Center the ordinary Taylor series at the coordinate `x` and regard its
indeterminate as a differential constant. -/
def expansion (x y : L) (d : ℕ) : L[X] :=
  ∑ i ∈ range (d+1), C (dividedDerivative y i) * (X-C x)^i

private theorem divided_deriv (y : L) (i : ℕ) :
    (dividedDerivative y i)′ = (Differential.deriv^[i+1]) y / i.factorial := by
  simpa only [dividedDerivative, Function.iterate_succ_apply', smul_eq_mul, div_eq_inv_mul] using
    (Differential.deriv.leibniz_div_const ((Differential.deriv^[i]) y) (i.factorial : L)
      (Differential.deriv.map_natCast i.factorial))

private theorem divided_succ (y : L) (i : ℕ) (hi : ((i+1).factorial : L) ≠ 0) :
    (dividedDerivative y i)′ = (↑(i+1) : L)*dividedDerivative y (i+1) := by
  rw [divided_deriv, dividedDerivative, Nat.factorial_succ, Nat.cast_mul] at *
  have hn : (↑(i+1) : L) ≠ 0 := left_ne_zero_of_mul hi
  have hm : (↑i.factorial : L) ≠ 0 := right_ne_zero_of_mul hi
  field_simp

private theorem expansion_mapCoeffs (x y : L) (hx : x′ = 1) (d : ℕ)
    (hn : ∀ i ≤ d, (i.factorial : L) ≠ 0) :
    Differential.mapCoeffs (expansion x y d) =
      C ((dividedDerivative y d)′) * (X-C x)^d := by
  induction d with
  | zero => simp [expansion]
  | succ d ih =>
      rw [expansion, sum_range_succ, map_add]
      change Differential.mapCoeffs (expansion x y d) + _ = _
      rw [ih (fun i hi => hn i (by omega)), divided_succ y d (hn (d+1) le_rfl)]
      rw [Differential.mapCoeffs.leibniz, Differential.mapCoeffs.leibniz_pow]
      simp only [Differential.mapCoeffs_C, map_mul, map_natCast, map_sub,
        Differential.mapCoeffs_X, hx, map_one, zero_sub, Nat.add_sub_cancel,
        smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring

/-- Every coefficient of the explicit expansion, including those past its
degree. Each summand is a divided derivative times one scalar monomial. -/
theorem coeff_expansion (x y : L) (d j : ℕ) :
    (expansion x y d).coeff j =
      ∑ i ∈ range (d+1), dividedDerivative y i * ((-x)^(i-j) * (i.choose j : L)) := by
  simp only [expansion, finsetSum_coeff, coeff_C_mul, sub_eq_add_neg, ← C_neg,
    coeff_X_add_C_pow]

theorem expansion_eval (x y : L) (d : ℕ) : (expansion x y d).eval x = y := by
  induction d with
  | zero => simp [expansion, dividedDerivative]
  | succ d ih =>
      rw [expansion, sum_range_succ, eval_add]
      change (expansion x y d).eval x + _ = y
      simp [ih]

theorem expansion_natDegree_le (x y : L) (d : ℕ) : (expansion x y d).natDegree ≤ d := by
  induction d with
  | zero => simp [expansion]
  | succ d ih =>
      rw [expansion, sum_range_succ]
      apply natDegree_add_le_of_degree_le
      · change (expansion x y d).natDegree ≤ d+1
        omega
      · apply (natDegree_C_mul_le _ _).trans
        simp

/-- Kernel of the order-`d+1` differential operator yields the actual explicit
polynomial with flat coefficients over any field where these factorials are units. -/
theorem expansion_coeff_flat (x y : L) (hx : x′ = 1) (d : ℕ)
    (hn : ∀ i ≤ d, (i.factorial : L) ≠ 0) (hy : (Differential.deriv^[d+1]) y = 0) (j : ℕ) :
    ((expansion x y d).coeff j)′ = 0 := by
  have hz := expansion_mapCoeffs x y hx d hn
  rw [divided_deriv, hy, zero_div, map_zero, zero_mul] at hz
  exact congrArg (fun q : L[X] => q.coeff j) hz

/-- Positive-characteristic specialization of the expansion and its flatness. -/
theorem expansion_spec {p : ℕ} [CharP L p] (hp : p.Prime) (x y : L) (hx : x′ = 1)
    (d : ℕ) (hd : d < p) (hy : (Differential.deriv^[d+1]) y = 0) :
    (expansion x y d).natDegree ≤ d ∧ (expansion x y d).eval x = y ∧
      ∀ j, ((expansion x y d).coeff j)′ = 0 := by
  refine ⟨expansion_natDegree_le x y d, expansion_eval x y d, expansion_coeff_flat x y hx d ?_ hy⟩
  intro i hi h0
  have hdiv := (CharP.cast_eq_zero_iff L p i.factorial).mp h0
  exact (Nat.not_le_of_lt (lt_of_le_of_lt hi hd)) (hp.dvd_factorial.mp hdiv)

end ArkLib.ProximityGap.Frontier.InverseTaylorFlat

open ArkLib.ProximityGap.Frontier.InverseTaylorFlat in
#print axioms expansion_spec
