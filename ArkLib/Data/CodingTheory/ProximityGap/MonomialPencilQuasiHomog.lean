/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Monomial-pencil μ_d-quasi-homogeneity (#407 — coset-saturation piece (2) structural core)

The Kambiré δ* optimality reduces (piece (2), "coset-saturation") to: for a MONOMIAL pencil
`U = X^a + γ·X^b` on `μ_n`, beyond Johnson, every large agreement set is a union of `μ_d`-cosets,
`d = gcd(a−b, n)`.  This file proves the two elementary STRUCTURAL halves of the easy direction:

* **`monomialPencil_quasi_homogeneous`** (pencil side) — if `ω^(a−b) = 1` then
  `(ω·x)^a + γ·(ω·x)^b = ω^a · (x^a + γ·x^b)`  (so `U(ωx) = ω^a U(x)`).
* **`expand_eval_mu_d_invariant`** (codeword side) — a `d`-sparse polynomial `expand R d g`
  (a polynomial in `Xᵈ`) is `μ_d`-eval-invariant:
  `(expand R d g).eval (ω·x) = (expand R d g).eval x` for `ω^d = 1`.

Together with the proven `FactorizationRigidity`, the agreement of `U` with the `a`-residue codeword
part `c_a = X^{a₀}·(expand R d g)` (`a₀ = a mod d`) transports along every `μ_d`-orbit, so that
agreement set is a union of `μ_d`-cosets.  This reduces piece (2) to a Johnson bound on the
OFF-residue codeword part — replacing the analytic char-`p`/Gauss-sum (Burgess) wall with
combinatorics.
Verified `scripts/probes/probe_coset_sat_structure.py` (12/12, n=16,32,64).  Axiom-clean.
-/

namespace ArkLib.ProximityGap.MonomialPencilQuasiHomog

open Polynomial

/-- **Monomial-pencil μ_d-quasi-homogeneity (pencil side).** If `ω^(a−b) = 1` (so `ω^a = ω^b`, e.g.
`ω ∈ μ_d`, `d ∣ a−b`), then `U(ω·x) = ω^a · U(x)` for the pencil `U = X^a + γ·X^b`. -/
theorem monomialPencil_quasi_homogeneous {R : Type*} [CommRing R] (a b : ℕ) (hab : b ≤ a)
    (ω x γ : R) (hω : ω ^ (a - b) = 1) :
    (ω * x) ^ a + γ * (ω * x) ^ b = ω ^ a * (x ^ a + γ * x ^ b) := by
  have hωab : ω ^ a = ω ^ b := by
    have h : ω ^ a = ω ^ (a - b) * ω ^ b := by
      rw [← pow_add]; congr 1; omega
    rw [h, hω, one_mul]
  rw [mul_pow, mul_pow, hωab]; ring

/-- The agreement condition `U = c` transports along the `μ_d`-orbit: `U(ωx) = ω^a · c(x)`. -/
theorem agreement_orbit_condition {R : Type*} [CommRing R] (a b : ℕ) (hab : b ≤ a)
    (ω x γ : R) (hω : ω ^ (a - b) = 1) (c : R) (hagree : x ^ a + γ * x ^ b = c) :
    (ω * x) ^ a + γ * (ω * x) ^ b = ω ^ a * c := by
  rw [monomialPencil_quasi_homogeneous a b hab ω x γ hω, hagree]

/-- **Codeword side: `d`-sparse eval-invariance.** A polynomial in `Xᵈ` is invariant under
`x ↦ ω·x` for any `ω` with `ω^d = 1`.  (Complements `FactorizationRigidity`'s root face.) -/
theorem expand_eval_mu_d_invariant {R : Type*} [CommRing R] {d : ℕ} (g : R[X]) {ω x : R}
    (hω : ω ^ d = 1) :
    (expand R d g).eval (ω * x) = (expand R d g).eval x := by
  rw [expand_eval, expand_eval, mul_pow, hω, one_mul]

end ArkLib.ProximityGap.MonomialPencilQuasiHomog
