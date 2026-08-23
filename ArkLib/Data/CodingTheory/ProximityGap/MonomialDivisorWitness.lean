/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The divisor-graded interior witness (#371): the explicit construction

The constructive half of the SPECTRUM = −μ_n law, discovered by configuration
extraction (`probe_wb_spectrum_odd_n_discrimination.py` round): at the interior
slice of agreement `d + 1` (a divisor `d` of the subgroup order), the monomial
line `x^{2d}·(x − x₀)` agrees with the **degree-one codeword** `A²·(x − x₀)` on
the `d + 1` domain points `{x₀} ∪ c₁μ_d`, via the one-line identity

  `x^{2d}(x − x₀) − A²(x − x₀) = (x − x₀)(x^{2d} − A²)`,

whose right side vanishes on `{x₀} ∪ (roots of x^{2d} = A²)` ⊇ `{x₀} ∪ c₁μ_d`
whenever `c₁^{2d} = A²`.  The probe-extracted structure: the free cofactor roots
are the complementary coset `c₂μ_d` with `c₂^d = −c₁^d` (verified exactly:
`11³ ≡ −1`, count `18 = 3 cosets × 6 anchor points` at `(37, μ₉)`), the
power-sum cancellation `d(c₁^d + c₂^d) = 0` in closed form — no Newton
machinery needed.

This file proves the agreement identity for arbitrary fields and parameters:
`monomial_divisor_agreement` — the line at `γ = −x₀` agrees with a codeword of
degree ≤ 1 on every point of `{x₀} ∪ {x : x^{2d} = A²}`.  Consumers instantiate
with `A := c₁^d`, `c₁ ∈ μ_n`, `d ∣ n` to land `d + 1` domain agreements at the
slice `w = n − d − 1`: the divisor-graded interior spectrum lower bound, and
the explanation of the supply arithmetic (`s = 2d + 1`; no integer `d` at
`s = 6`, hence the measured emptiness).
-/

open Polynomial

namespace ProximityGap.MonomialDivisorWitness

variable {F : Type} [Field F]

/-- **The agreement identity**: the monomial line `x^{2d}(x − x₀)` (the stack
`(x^{2d+1}, x^{2d})` at scalar `γ = −x₀`) differs from the degree-≤1 codeword
`A²(x − x₀)` by `(x − x₀)(x^{2d} − A²)`. -/
theorem line_sub_codeword (d : ℕ) (x₀ A : F) :
    (X ^ (2 * d + 1) + C (-x₀) * X ^ (2 * d))
        - (C (A ^ 2) * X - C (A ^ 2 * x₀))
      = (X - C x₀) * (X ^ (2 * d) - C (A ^ 2)) := by
  rw [C_neg, C_mul]
  ring

/-- **The pointwise agreement**: at every point `x` with `x = x₀` or
`x^{2d} = A²`, the monomial line at scalar `−x₀` equals the codeword
`A²(x − x₀)`. -/
theorem monomial_divisor_agreement (d : ℕ) (x₀ A : F) (x : F)
    (hx : x = x₀ ∨ x ^ (2 * d) = A ^ 2) :
    x ^ (2 * d + 1) + (-x₀) * x ^ (2 * d) = A ^ 2 * x - A ^ 2 * x₀ := by
  have h := congrArg (Polynomial.eval x) (line_sub_codeword d x₀ A)
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at h
  have hzero : (x - x₀) * (x ^ (2 * d) - A ^ 2) = 0 := by
    rcases hx with h1 | h2
    · rw [h1, sub_self, zero_mul]
    · rw [h2, sub_self, mul_zero]
  rw [hzero] at h
  exact sub_eq_zero.mp h

/-- **Coset form of the divisor witness**: if `c^(2d) = A²`, then the whole
`μ_d`-coset `c·μ_d` consists of agreement points for the monomial line at
scalar `−x₀`. -/
theorem monomial_divisor_agreement_coset (d : ℕ) (x₀ A c ζ : F)
    (hc : c ^ (2 * d) = A ^ 2) (hζ : ζ ^ d = 1) :
    (c * ζ) ^ (2 * d + 1) + (-x₀) * (c * ζ) ^ (2 * d)
      = A ^ 2 * (c * ζ) - A ^ 2 * x₀ := by
  refine monomial_divisor_agreement d x₀ A (c * ζ) (Or.inr ?_)
  have hζ2d : ζ ^ (2 * d) = 1 := by
    rw [Nat.mul_comm 2 d, pow_mul, hζ, one_pow]
  rw [mul_pow, hc, hζ2d, mul_one]

/-- Membership form for the anchor-plus-coset agreement set. -/
theorem monomial_divisor_agreement_anchor_or_coset (d : ℕ) (x₀ A c x : F)
    (hc : c ^ (2 * d) = A ^ 2)
    (hx : x = x₀ ∨ ∃ ζ : F, ζ ^ d = 1 ∧ x = c * ζ) :
    x ^ (2 * d + 1) + (-x₀) * x ^ (2 * d) = A ^ 2 * x - A ^ 2 * x₀ := by
  rcases hx with hx₀ | ⟨ζ, hζ, hxζ⟩
  · exact monomial_divisor_agreement d x₀ A x (Or.inl hx₀)
  · rw [hxζ]
    exact monomial_divisor_agreement_coset d x₀ A c ζ hc hζ

end ProximityGap.MonomialDivisorWitness

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MonomialDivisorWitness.line_sub_codeword
#print axioms ProximityGap.MonomialDivisorWitness.monomial_divisor_agreement
#print axioms ProximityGap.MonomialDivisorWitness.monomial_divisor_agreement_coset
#print axioms ProximityGap.MonomialDivisorWitness.monomial_divisor_agreement_anchor_or_coset
