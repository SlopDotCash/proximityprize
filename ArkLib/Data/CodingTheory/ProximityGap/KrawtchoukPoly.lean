/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Krawtchouk polynomials (machinery for the Shaw-operator / Proximity Prize, #389)

The `q`-ary Krawtchouk value `K_k(x)` (ambient length `n`) is the coefficient of `z^k` in
`(1 + (q−1)z)^{n−x} · (1 − z)^x` — equivalently the explicit alternating binomial sum below. It is
the Fourier transform of the Hamming weight-`k` shell evaluated at character-weight `x`; the prize's
Shaw operator is a Krawtchouk-weighted dual-MDS character sum. Defined here with its closed
generating form. Axiom-clean.
-/
set_option linter.style.longLine false


open Polynomial Finset

namespace ArkLib.ProximityGap.Krawtchouk

/-- The `q`-ary Krawtchouk value `K_k(x)` (ambient length `n`), explicit binomial form (antidiagonal
indexing matching the generating function `(1+(q−1)z)^{n−x}(1−z)^x`). -/
def krawtchouk (q n x k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1),
    ((n - x).choose j : ℤ) * ((q : ℤ) - 1) ^ j * (x.choose (k - j) : ℤ) * (-1) ^ (k - j)

/-- Binomial coefficient extraction: `coeff a of (1 + c·X)^m = C(m,a)·c^a`. -/
theorem coeff_one_add_C_mul_X_pow {R : Type*} [CommRing R] (c : R) (m a : ℕ) :
    ((1 + C c * X) ^ m).coeff a = (m.choose a : R) * c ^ a := by
  rw [add_comm, add_pow, finset_sum_coeff]
  have hterm : ∀ b ∈ Finset.range (m + 1),
      ((C c * X) ^ b * (1 : R[X]) ^ (m - b) * (m.choose b : R[X])).coeff a
        = if a = b then (m.choose b : R) * c ^ b else 0 := by
    intro b _
    rw [one_pow, mul_one, mul_pow, ← C_pow,
      show ((m.choose b : ℕ) : R[X]) = C ((m.choose b : R)) by simp,
      coeff_mul_C, coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq (Finset.range (m + 1)) a
      (fun b => (m.choose b : R) * c ^ b)]
  split_ifs with h
  · rfl
  · rw [mem_range, not_lt] at h
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

/-- **The Krawtchouk generating function (closed form).** `K_k(x) = [z^k] (1+(q−1)z)^{n−x}(1−z)^x`. -/
theorem krawtchouk_eq_coeff (q n x k : ℕ) :
    ((1 + C ((q : ℤ) - 1) * X) ^ (n - x) * (1 - X) ^ x).coeff k = krawtchouk q n x k := by
  rw [show (1 - (X : ℤ[X])) = 1 + C (-1 : ℤ) * X by rw [C_neg, C_1]; ring, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, krawtchouk]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  dsimp only
  rw [coeff_one_add_C_mul_X_pow, coeff_one_add_C_mul_X_pow]; ring

end ArkLib.ProximityGap.Krawtchouk

#print axioms ArkLib.ProximityGap.Krawtchouk.krawtchouk_eq_coeff
