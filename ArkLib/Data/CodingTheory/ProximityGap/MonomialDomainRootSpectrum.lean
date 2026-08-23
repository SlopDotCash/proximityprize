/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-!
# Monomial domain-root spectrum

The j-fold-deficient probes for the monomial adversary isolate a simple mechanism:
below the capacity cliff, bad scalars are forced into the smooth-domain subgroup because
the line `x^b (x + γ)` has a root on the evaluation domain.  This file formalizes the
root-to-spectrum half of that mechanism.

For the polynomial `X^(b+1) + γ X^b`, any nonzero root `x` forces `γ = -x`.
Therefore, on an even `n`-th-root domain, such a `γ` satisfies `γ^n = 1`; if the
domain is closed under negation, it is literally a domain element.
-/

open Polynomial

namespace ProximityGap.MonomialSpectrum

variable {F : Type} [Field F]

/-- The monomial line `X^(b+1) + γ X^b = X^b (X + γ)`. -/
noncomputable def monomialLineFrom (b : ℕ) (γ : F) : F[X] :=
  X ^ (b + 1) + C γ * X ^ b

/-- Evaluation factorization for the monomial line. -/
theorem monomialLineFrom_eval (b : ℕ) (γ x : F) :
    (monomialLineFrom b γ).eval x = x ^ b * (x + γ) := by
  simp only [monomialLineFrom, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  rw [pow_succ]
  ring

/-- If `γ = -x`, then `x` is a root of the monomial line. -/
theorem monomialLineFrom_eval_eq_zero_of_gamma_eq_neg {b : ℕ} {γ x : F}
    (hγ : γ = -x) :
    (monomialLineFrom b γ).eval x = 0 := by
  rw [monomialLineFrom_eval, hγ, add_neg_cancel, mul_zero]

/-- Conversely, a nonzero root of the monomial line pins `γ = -x`. -/
theorem gamma_eq_neg_of_monomialLineFrom_eval_eq_zero {b : ℕ} {γ x : F}
    (hx : x ≠ 0) (hroot : (monomialLineFrom b γ).eval x = 0) :
    γ = -x := by
  rw [monomialLineFrom_eval] at hroot
  have hxpow : x ^ b ≠ 0 := pow_ne_zero b hx
  have hxγ : x + γ = 0 := (mul_eq_zero.mp hroot).resolve_left hxpow
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm] using hxγ

/-- Even-order root domains are closed under negation at the level of the equation
`x^n = 1`. -/
theorem neg_pow_eq_one_of_even {n : ℕ} (hn : Even n) {x : F} (hx : x ^ n = 1) :
    (-x) ^ n = 1 := by
  simpa [hx] using hn.neg_pow x

/-- A nonzero domain root of the monomial line forces the scalar into the same
even-order root equation. -/
theorem gamma_pow_eq_one_of_monomialLineFrom_domain_root {b n : ℕ} (hn : Even n)
    {γ x : F} (hx : x ≠ 0) (hxroot : x ^ n = 1)
    (hroot : (monomialLineFrom b γ).eval x = 0) :
    γ ^ n = 1 := by
  rw [gamma_eq_neg_of_monomialLineFrom_eval_eq_zero hx hroot]
  exact neg_pow_eq_one_of_even hn hxroot

/-- Root-set form: if the monomial line has a nonzero root in a domain `D`, then its
scalar lies in the negated image of `D`. -/
theorem gamma_mem_neg_image_of_monomialLineFrom_domain_root [DecidableEq F]
    {b : ℕ} {γ : F} (D : Finset F) (hDnz : ∀ x ∈ D, x ≠ 0)
    (hroot : ∃ x ∈ D, (monomialLineFrom b γ).eval x = 0) :
    γ ∈ D.image (fun x : F => -x) := by
  rcases hroot with ⟨x, hxD, hxroot⟩
  refine Finset.mem_image.mpr ?_
  exact ⟨x, hxD, (gamma_eq_neg_of_monomialLineFrom_eval_eq_zero (hDnz x hxD) hxroot).symm⟩

/-- If the domain is negation-closed, the same root condition puts `γ` back in `D`. -/
theorem gamma_mem_domain_of_monomialLineFrom_domain_root
    {b : ℕ} {γ : F} (D : Finset F) (hDnz : ∀ x ∈ D, x ≠ 0)
    (hDneg : ∀ x ∈ D, -x ∈ D)
    (hroot : ∃ x ∈ D, (monomialLineFrom b γ).eval x = 0) :
    γ ∈ D := by
  rcases hroot with ⟨x, hxD, hxroot⟩
  rw [gamma_eq_neg_of_monomialLineFrom_eval_eq_zero (hDnz x hxD) hxroot]
  exact hDneg x hxD

/-- Finite-domain root-equation form: if every domain point is an `n`-th root of unity
and `n` is even, any scalar with a nonzero domain root satisfies `γ^n = 1`. -/
theorem gamma_pow_eq_one_of_domain_root {b n : ℕ} (hn : Even n)
    {γ : F} (D : Finset F) (hDnz : ∀ x ∈ D, x ≠ 0)
    (hDroot : ∀ x ∈ D, x ^ n = 1)
    (hroot : ∃ x ∈ D, (monomialLineFrom b γ).eval x = 0) :
    γ ^ n = 1 := by
  rcases hroot with ⟨x, hxD, hxroot⟩
  exact gamma_pow_eq_one_of_monomialLineFrom_domain_root hn (hDnz x hxD)
    (hDroot x hxD) hxroot

end ProximityGap.MonomialSpectrum

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialSpectrum.monomialLineFrom_eval
#print axioms ProximityGap.MonomialSpectrum.gamma_eq_neg_of_monomialLineFrom_eval_eq_zero
#print axioms ProximityGap.MonomialSpectrum.gamma_mem_domain_of_monomialLineFrom_domain_root
#print axioms ProximityGap.MonomialSpectrum.gamma_pow_eq_one_of_domain_root
