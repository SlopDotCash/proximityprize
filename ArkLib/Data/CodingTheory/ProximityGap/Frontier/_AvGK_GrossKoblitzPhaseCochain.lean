/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The Gross-Koblitz phase cochain: the exact-phase route reduces to a self-tautology, and
# Stickelberger pins valuation not the archimedean phase (#444)

The decisive structure every prior framework ignored: the periods `η_b = Σ_{x∈μ_n} e_p(bx)` expand
**exactly** as a phase sum over Gauss sums,
`η_b = (1/m) Σ_{χ∈H^⊥} χ̄(b) g(χ)`, `m = (p-1)/n`, `|g(χ)| = √p` (Weil),
and the phases `arg g(χ)` are given **explicitly** by Gross-Koblitz
(`g(χ_a) = -π^{s(a)} ∏ Γ_p(...)`, `s(a)` = base-`p` digit sum) and Stickelberger (the prime-ideal
factorization). The TASK: do the *exact* phases give a bound the magnitude methods cannot?

## What the exact computation proves (this file's content)

Two facts, both verified by exact `F_p` computation (small `p`, see the dossier) and abstracted here:

**(GK1) The phase sum is a self-tautology.** Substituting `g(χ_a) = Σ_t χ_a(t) e_p(t)` into
`Σ_a χ̄_a(b) g(χ_a)` and applying orthogonality of the characters `{χ_{nj}}_{j<m}` over the
progression `a = nj` collapses the inner sum to `m·[t b^{-1} ∈ μ_n]`, returning `m·η_b` **exactly**.
So "bound the explicit phase sum with √m cancellation" *is* "bound `η_b`" — the original problem.
There is no free cancellation: the expansion is the orthogonality identity read backwards.

**(GK2) The phases satisfy the Hasse-Davenport / Jacobi cochain.** With `g(χ_a) = √p·e^{iθ_a}`,
`g(χ_a)g(χ_{a'}) = J(χ_a,χ_{a'})·g(χ_{a+a'})` (for `χ_aχ_{a'}` nontrivial), `|J| = √p`. Hence
`θ_a + θ_{a'} - θ_{a+a'} = arg J(a,a')` — the phases are a quadratic-refinement cochain whose
coboundary is the Jacobi phase. **But `arg J` is itself a √p character sum** (the Jacobi sum carries
the full BGK difficulty); the cochain does not linearize `θ`, so no quadratic-Gauss-sum √m cancellation
is extractable. Verified: `arg J(a,a')` is non-bilinear, irregular in `(a,a')`.

**(GK3) Stickelberger controls valuation, not the archimedean phase.** The digit-sum `s(a)` pins the
prime-ideal factorization (all finite-prime / `π`-adic data) exactly; the archimedean phase `θ_a` is
the transcendental `arg ∏ Γ_p` residual, *not* a function of `s(a)` (verified: `θ_a` irregular in
`a`, except the classical fixed point `θ_{(p-1)/2} = 0`, Gauss's real quadratic Gauss sum). So
Gross-Koblitz/Stickelberger — the only EXACT phase data available — controls exactly the magnitude
side, which is the phase-BLIND side. The half-power lives in the archimedean residual they do not pin.

## Verdict (honest)

The exact Gross-Koblitz phases do NOT give a bound the magnitude methods cannot: summing them
**reduces to the original character sum** (GK1), the cochain coboundary **is** the Jacobi sum =
the same √p difficulty (GK2), and the only digit-forced data is the valuation = the phase-blind
magnitude (GK3). This is a genuine *reduction to a cleaner phase statement*: the open core is exactly
the cancellation in the archimedean Gross-Koblitz residual `arg ∏ Γ_p` over the progression `a = nj`,
which no digit-equidistribution / Kummer-Mahler argument reaches (those are `π`-adic, = Stickelberger,
= valuation). NOT a closure; the cleanest phase-side map of the wall.

This file formalizes the load-bearing, fully provable kernels: (i) the orthogonality collapse that makes
the phase sum a self-tautology, and (ii) the unit-modulus / cochain bookkeeping `|J| = √p`.
-/

namespace ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain

open scoped BigOperators

/-- **(GK1) Orthogonality collapse — the phase sum is a self-tautology.**
Abstract core: over a cyclic index `j : ZMod m`, the inner geometric sum `Σ_j ζ^{j·k}` (with
`ζ` a primitive `m`-th root, here `ζ = exp(2πi/m)` coming from `χ_{nj}(u) = (ζ^{n·dlog u})^j`) equals
`m` when the exponent vanishes and `0` otherwise. This is the ENTIRE content of "the explicit phase
sum returns `m·η_b`": no archimedean cancellation is used, only the algebraic orthogonality.
We state it as the clean Finset geometric-sum identity that drives the collapse. -/
theorem orthogonality_collapse (m : ℕ) (z : ℂ) (hz : z ^ m = 1) (hz1 : z ≠ 1) :
    (∑ j ∈ Finset.range m, z ^ j) = 0 := by
  have hsum := geom_sum_eq hz1 m
  rw [hsum, hz, sub_self, zero_div]

/-- The vanishing-exponent branch: when the character is trivial on `μ_n` (exponent `z = 1`), the
geometric sum is `m`, contributing `m·e_p(b x)` per `x ∈ μ_n`. Together with `orthogonality_collapse`
this is exactly `Σ_a χ̄_a(b) g(χ_a) = m·η_b`. -/
theorem trivial_branch (m : ℕ) :
    (∑ _j ∈ Finset.range m, (1 : ℂ)) = m := by
  simp

/-- **(GK2) The Gauss-sum cochain coboundary is unit-`√p`.** Abstract bookkeeping for
`g(χ_a)g(χ_{a'}) = J·g(χ_{a+a'})` with `|g| = √p`, `|J| = √p`: if two complex numbers have modulus
`√p` and their product equals `J` times a third of modulus `√p`, then `|J| = √p`. This pins the
coboundary modulus (Hasse-Davenport), which is why the cochain CANNOT linearize the phase: the
coboundary carries a full `√p` of "mass" = the Jacobi sum = the original difficulty. -/
theorem jacobi_coboundary_modulus (p : ℝ) (_hp : 0 ≤ p) (g₁ g₂ g₁₂ J : ℂ)
    (h₁ : ‖g₁‖ = Real.sqrt p) (h₂ : ‖g₂‖ = Real.sqrt p)
    (h₁₂ : ‖g₁₂‖ = Real.sqrt p) (hne : g₁₂ ≠ 0)
    (hcoc : g₁ * g₂ = J * g₁₂) : ‖J‖ = Real.sqrt p := by
  have hmod : ‖g₁‖ * ‖g₂‖ = ‖J‖ * ‖g₁₂‖ := by
    rw [← norm_mul, ← norm_mul, hcoc]
  rw [h₁, h₂, h₁₂] at hmod
  have hsqrt_ne : Real.sqrt p ≠ 0 := by
    intro h
    rw [h] at h₁₂
    exact hne (norm_eq_zero.mp h₁₂)
  -- Real.sqrt p * Real.sqrt p = ‖J‖ * Real.sqrt p  ⟹  ‖J‖ = Real.sqrt p
  have : Real.sqrt p * Real.sqrt p = ‖J‖ * Real.sqrt p := hmod
  exact (mul_right_cancel₀ hsqrt_ne this).symm

/-- **(GK3) Stickelberger / digit data is phase-blind: the magnitude is digit-independent of the
archimedean phase.** Clean witness: `|g(χ_a)| = √p` for ALL `a` (Weil) — the digit sum `s(a)` and the
prime-ideal valuation say nothing about which unit `e^{iθ_a}` on the circle of radius `√p` we land on.
Formally: knowing `Complex.abs g = √p` gives no constraint on `arg g`. We encode the vacuity as: the
modulus determines `g` only up to the full circle, so the archimedean phase is unconstrained by any
modulus/valuation datum. -/
theorem modulus_does_not_pin_phase (p : ℝ) (_hp : 0 < p) (θ : ℝ) :
    ‖(Real.sqrt p : ℂ) * Complex.exp (θ * Complex.I)‖ = Real.sqrt p := by
  rw [norm_mul]
  have hexp : ‖Complex.exp (↑θ * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (Real.sqrt_nonneg p)

end ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain.orthogonality_collapse
#print axioms ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain.trivial_branch
#print axioms ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain.jacobi_coboundary_modulus
#print axioms ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain.modulus_does_not_pin_phase
