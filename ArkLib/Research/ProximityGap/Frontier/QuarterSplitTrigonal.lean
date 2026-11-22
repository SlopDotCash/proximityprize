/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! # Algebra of the unlabelled trigonal test for a split pencil

A simple union of three fibers gives a map to the cubic `v³ = u(u−1)`.
For an even-genus curve with an even Frobenius polynomial, a zero of its
reciprocal polynomial at the negative center is at least a double zero.
The geometric quotient and Frobenius arguments are in the accompanying note. -/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.QuarterSplitTrigonal

open Polynomial Finset

/-- On the affine chart of a split pencil the cubic coordinates satisfy the elliptic equation. -/
theorem cubic_map {K : Type*} [Field K] {P Q y : K} (hQ : Q ≠ 0)
    (hy : y ^ 3 = P * Q * (P - Q)) :
    (y / Q) ^ 3 = (P / Q) * (P / Q - 1) := by
  field_simp
  linear_combination hy

/-- Three marked fibers of degree at most h can receive 3D fixed points only when h ≥ D.
At the minimum each of the three fibers is exhausted. -/
theorem fixed_fiber_capacity {D h s₀ s₁ s₂ : ℕ} (hcard : s₀+s₁+s₂ = 3*D)
    (h₀ : s₀ ≤ h) (h₁ : s₁ ≤ h) (h₂ : s₂ ≤ h) :
    D ≤ h ∧ (h = D → s₀ = D ∧ s₁ = D ∧ s₂ = D) := by omega

/-- Equal reciprocal coefficients pair across the central exponent in the Weil polynomial. -/
private theorem reciprocal_term {K : Type*} [CommRing K] (u q : K) (k j : ℕ) :
    u^k * (u^(2*j) + q^(2*j)) =
      u^k * (u^j - q^j)^2 + (2*q^j)*u^(k+j) := by
  rw [pow_add, Nat.mul_comm 2 j, pow_mul, pow_mul]
  ring

/-- A reciprocal polynomial of even degree, written as its central term and paired terms.
The center q is −p when applying the functional equation to G with F(X)=G(X²). -/
noncomputable def reciprocalPolynomial {K : Type*} [CommRing K] (q c : K) (m : ℕ)
    (b : ℕ → K) : K[X] :=
  C c * X^m + ∑ i ∈ range m, C (b i) * (X^(m-(i+1)) *
    (X^(2*(i+1)) + C q^(2*(i+1))))

/-- A zero at the center of an even-degree reciprocal polynomial has multiplicity at least two. -/
theorem center_square {K : Type*} [Field K] {q c : K} (hq : q ≠ 0) (m : ℕ)
    (b : ℕ → K) (hzero : (reciprocalPolynomial q c m b).eval q = 0) :
    (X - C q)^2 ∣ reciprocalPolynomial q c m b := by
  let k (i : ℕ) := m-(i+1)
  let A : K[X] := ∑ i ∈ range m, (C (b i) * X^(k i)) * (X^(i+1) - (C q)^(i+1))^2
  let M : K := c + ∑ i ∈ range m, b i * (2*q^(i+1))
  have hrep : reciprocalPolynomial q c m b = A + C M * X^m := by
    simp only [reciprocalPolynomial, A, M, map_add, map_sum, add_mul, sum_mul]
    conv_rhs => rw [add_left_comm]
    apply congrArg (C c * X^m + ·)
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have he : k i + (i+1) = m := by
      have := mem_range.mp hi
      dsimp [k]
      omega
    rw [reciprocal_term]
    change C (b i) * (_ + _ * X ^ (k i + (i+1))) = _
    rw [he]
    simp only [map_mul, map_pow, map_ofNat]
    ring
  have hA : (X-C q)^2 ∣ A := by
    apply Finset.dvd_sum
    intro i _
    apply dvd_mul_of_dvd_right
    apply pow_dvd_pow_of_dvd
    simpa using (X_sub_C_dvd_sub_C_eval (p := (X : K[X])^(i+1)) (a := q))
  have hzA : A.eval q = 0 := by
    obtain ⟨W, hW⟩ := hA
    rw [hW]
    simp
  have hzM : M = 0 := by
    rw [hrep, eval_add, hzA, zero_add, eval_mul] at hzero
    simpa [hq] using hzero
  simpa [hrep, hzM] using hA

/-- The genus-four trace test needs only the two even point counts N₂ and N₄. -/
theorem genus_four_remainder {K : Type*} [CommRing K] (u p a b : K) :
    u^4+a*u^3+b*u^2+p^2*a*u+p^4 =
      (u+p)^2 * (u^2+(a-2*p)*u+p^2) + (b-2*p*a+2*p^2)*u^2 := by ring

#print axioms cubic_map
#print axioms fixed_fiber_capacity
#print axioms center_square
#print axioms genus_four_remainder

end ArkLib.ProximityGap.Frontier.QuarterSplitTrigonal
