/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (Av-CS frontier — the Chowla-Selberg / CM-period / Γ-value data
is phase-blind for `M`; it pins the Galois-orbit PRODUCT, not the individual Gauss-sum phases)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Av-CS — Chowla-Selberg / CM-period Γ-values are PHASE-BLIND for `M` (#444)

## FRESH AVENUE: CM_PERIOD_CHOWLA_SELBERG

The campaign's open core is `M = max_{b≠0} |η_b|`, `η_b = Σ_{x∈μ_n} e_p(b x)`, with the period
identity (exactly verified, `scripts` `cs2.py`, max reconstruction error `< 2·10⁻¹³`):

  `η_b = (1/N) · Σ_{a=0}^{N-1} χ̄^a(b) · g(χ^a)`,   `N = (p-1)/n`,

so `M` is the worst-case modulus of an `N`-term average of the Gauss sums `g(χ^a)`, each of
modulus `√p`. The CM_PERIOD avenue: the `g(χ^a)` are **CM periods of the cyclotomic curve**,
and Chowla-Selberg / Gross-Koblitz at the archimedean place expresses certain **products** of
them via `Γ(a/N)` values. The hope: `Γ`-value transcendence / distribution relations
(Rohrlich-Lang, the multiplication/reflection formulas, Deligne's CM-period bounds) reach the
archimedean phase `arg g(χ^a)` — the object the campaign says is unreachable — and bound `M`.

## VERDICT: REDUCES. The Γ-value / CM-period data is PHASE-BLIND for `M`.

What Chowla-Selberg / Gross-Koblitz / the Γ-multiplication formula ACTUALLY pin (all exactly
computed, `scripts` `cs5.py`, `cs7b.py`):

1. **Radial datum.** `|g(χ^a)| = √p` for every `a ≠ 0` (the absolute value — the magnitude).
2. **Conjugate pairing (Stickelberger).** `g(χ^a)·g(χ^{-a}) = χ^a(-1)·p`, i.e.
   `arg g(χ^a) + arg g(χ^{-a}) ≡ 0 or π`. (Exactly: `g·ḡ/p = χ^a(-1) ∈ {±1}`, all `a`.)
3. **Galois-orbit PRODUCT (the CM period).**
   `∏_{a=1}^{N-1} g(χ^a) = (root of unity) · p^{(N-1)/2}`.
   Computed across `N ∈ {3,4,5,6}` and many primes: the product is ALWAYS `±1` or `±i` times
   `p^{(N-1)/2}` — i.e. its **argument is a discrete root of unity (the sign/Galois datum), and
   its magnitude is `p^{(N-1)/2}` (the Stickelberger valuation = the Γ-multiplication formula).**

This is the **entire** Γ-value content. None of it pins an INDIVIDUAL `arg g(χ^a)`.

**The decisive exact computation (`cs4.py`).** Fix `N = 5`. Across primes
`p ∈ {11,31,41,61,71,101}` (all `≡ 1 mod 5`, hence all sharing the SAME `Γ(a/5)` data), the
phase `arg g(χ^1)` takes the values
  `0.652, −0.614, 1.288, 2.426, 2.515, −0.418`
— **wildly different**, with no `Γ`-only pattern. The conjugate-pairing and product-phase
relations are the only invariants, and they leave a free archimedean phase torus of dimension
`⌊(N-1)/2⌋ − 1` (`= 0,1,2,4` for `N = 3,5,7,11`; `~ N/2 ~ n³/2` in the prize regime `N ~ n³`).

**And `M` is a NON-constant function on that free torus (`cs6.py`).** Sampling phase vectors that
respect ALL the CS/Γ constraints (radial, pairing, product-phase) and are otherwise free,
`M/√p` ranges over `[0.46, 0.80]` (`N=5`), `[0.40, 0.86]` (`N=7`), `[0.35, 0.89]` (`N=11`).
So fixing the complete Γ-value datum still leaves `M` ranging over an `Ω(1)`-wide band:
**the Γ-values do not determine `M`.** The `√(2n log N)` extreme-value behaviour the prize asks
about lives ENTIRELY in the free archimedean phases — exactly the deep-depth archimedean-phase
wall — which Chowla-Selberg does not touch.

This is the same phenomenon already recorded for Gross-Koblitz/Stickelberger in the ledger
(`phase-blind in provable part`): the Γ-multiplication formula IS the Stickelberger digit-sum,
which is the `p`-adic VALUATION = the radial magnitude, NOT the archimedean phase.

## What this brick proves (the structural core, axiom-clean)

The mechanism is a clean complex-analysis fact: **a constraint that fixes a PRODUCT of unit-
modulus-scaled phasors (the CM-period datum) does not bound the modulus of their SUM (which
controls `M`).** Concretely: one can rotate the individual phases by `θ_a` with `Σ θ_a ≡ 0`
(keeping the product, the radial moduli, and — choosing `θ` antisymmetric — the conjugate
pairing all fixed), yet drive the modulus of the average across an `Ω(1)` band. We formalize the
backbone: the product is invariant under a phase rotation summing to zero, while the sum is not,
so the product cannot serve as a bound on the sum's modulus. This is exactly why every Γ-value /
CM-period relation REDUCES to (does not evade) the archimedean-phase wall.
-/

namespace ArkLib.ProximityGap.Frontier.AvCS

open Complex

/-- **The CM-period datum is invariant under a zero-sum phase rotation.**
If we rotate each factor `z a` by a unit phase `Complex.exp (θ a * I)` whose total argument sums
to zero (`∑ θ a = 0`), the Galois-orbit product `∏ z a` is unchanged. This is the exact
invariance the Chowla-Selberg / Gross-Koblitz Γ-value relations enjoy: they pin `∏ g(χ^a)` (a
root of unity times `p^{(N-1)/2}`), which is blind to any redistribution of phase among the
factors that preserves the total. -/
theorem prod_rotate_eq_of_sum_zero {ι : Type*} (s : Finset ι) (z : ι → ℂ) (θ : ι → ℝ)
    (hθ : ∑ a ∈ s, θ a = 0) :
    ∏ a ∈ s, (Complex.exp (θ a * I) * z a) = ∏ a ∈ s, z a := by
  rw [Finset.prod_mul_distrib]
  have : ∏ a ∈ s, Complex.exp (θ a * I) = 1 := by
    rw [← Complex.exp_sum]
    have hcast : ∑ a ∈ s, ((θ a : ℂ) * I) = (↑(∑ a ∈ s, θ a) : ℂ) * I := by
      rw [← Finset.sum_mul, Complex.ofReal_sum]
    rw [hcast, hθ]
    simp
  rw [this, one_mul]

/-- **The SUM is NOT invariant under the same zero-sum phase rotation.** There is a concrete
two-factor configuration (`s = {0,1}`, `z = (1,1)`, `θ = (π/2, −π/2)`, which sums to zero) for
which the product is preserved (`= 1` both before and after) but the modulus of the sum collapses
from `2` to `0` (`exp(πI/2)·1 + exp(−πI/2)·1 = i + (−i) = 0`). Hence the product datum **cannot**
bound the modulus of the sum: the CM-period / Γ-value invariant is phase-blind for `M`. -/
theorem sum_not_determined_by_prod :
    ∃ (z : Fin 2 → ℂ) (θ : Fin 2 → ℝ),
      (∑ a, θ a = 0) ∧
      (∏ a, (Complex.exp (θ a * I) * z a) = ∏ a, z a) ∧
      (‖∑ a, z a‖ = 2) ∧
      (‖∑ a, (Complex.exp (θ a * I) * z a)‖ = 0) := by
  refine ⟨fun _ => 1, ![Real.pi / 2, -(Real.pi / 2)], ?_, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_two]
  · -- product preserved by `prod_rotate_eq_of_sum_zero`
    apply prod_rotate_eq_of_sum_zero
    simp [Fin.sum_univ_two]
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [show (1 : ℂ) + 1 = (2 : ℂ) by ring]
    simp
  · -- rotate by (π/2, -π/2): exp(π/2·I)·1 + exp(-π/2·I)·1 = I + (-I) = 0
    have h1 : Complex.exp (((Real.pi / 2 : ℝ) : ℂ) * I) = I := by
      rw [show (((Real.pi / 2 : ℝ) : ℂ) * I) = (↑(Real.pi / 2) * I) by push_cast; ring]
      rw [Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      ring
    have h2 : Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * I) = -I := by
      rw [show (((-(Real.pi / 2) : ℝ) : ℂ) * I) = (↑(-(Real.pi / 2)) * I) by push_cast; ring]
      rw [Complex.exp_mul_I]
      push_cast
      rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
      ring
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      mul_one]
    rw [h1, h2]
    rw [add_neg_cancel]
    simp

end ArkLib.ProximityGap.Frontier.AvCS
