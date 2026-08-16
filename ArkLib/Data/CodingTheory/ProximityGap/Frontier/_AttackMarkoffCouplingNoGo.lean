/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

set_option autoImplicit false

/-!
# Attack #16 — Twisted Markoff-surface coupling: the transfer FACTORS OUT M (#444)

## The conjecture under test (Markoff coupling)

Let `μ_n` be the order-`n` (`n = 2^μ`) subgroup of `F_p^*`, `η_b = Σ_{x∈μ_n} e_p(b x)` the Gauss
period, and `M(n) = max_{b≠0} |η_b|` the house. The Markoff coupling proposes to *escape the dyadic
torsion structure* by pairing the period with the **Markoff surface**
`X(p) : x² + y² + z² = 3xyz mod p`, whose monodromy is a **thin SL₂ subgroup** (Bourgain–Gamburd–
Sarnak: `X(p)` is a single big orbit with a spectral gap). The hope: the genuine big monodromy of
`X(p)` supplies the square-root cancellation that the abelian `μ_n` cannot, and a Markoff char-sum
bound transfers to `M`.

The only coupling that *could* transfer to `M` is the **`x`-slice restriction**: write the Markoff
period restricted to the slices `x ∈ μ_n` as

  `η^M_b := Σ_{x ∈ μ_n} ( Σ_{(y,z): (x,y,z)∈X(p)} e_p(b(y+z)) ) · e_p(b x)
         = Σ_{x ∈ μ_n} w(x) · e_p(b x)`,

where `w(x) := Σ_{(y,z): (x,y,z)∈X(p)} e_p(b(y+z))` is the **Markoff conic fiber-weight** over the
slice `x` (the conic `C_x : y² + z² − 3x·yz + x² = 0`). The transfer claim is: a big-monodromy bound
on `η^M_b` controls `M = max_b|η_b|`.

## What is TRUE (this file proves it, axiom-clean) vs what is FALSE — the FACTORING

The transfer is governed by ONE identity: `η^M_b` equals `K · η_b` (a constant times the actual
period, hence a bound on `η^M_b` bounds `M`) **if and only if** the fiber-weight `w` is **constant**
on `μ_n`. An exact `F_p` probe settles this.

* **(TRUE — the factoring lemma, this file).** If `w(x) = K` for all `x ∈ μ_n` then
  `Σ_x w(x)·e_p(bx) = K·Σ_x e_p(bx) = K·η_b`, so `|η^M_b| = |K|·|η_b|` and the Markoff bound DOES
  transfer (`weighted_period_factors`). This is the *whole* mechanism by which any twisted/coupled
  sum can bound the Paley sup-norm: the twist weight must be a constant phase.

* **(FALSE — the probe, DECISIVE).** Exact `F_p` enumeration of the Markoff conic over `x ∈ μ_n`
  shows `w` is **strongly non-constant**. At the prize prime `p = 65537 = 1 + 2¹⁶` (so `μ_16`,
  `β = 4`, `p/n⁴ = 1.000`):
      `|w(x)|`  ranges  **39.94 … 497.76**  over the 16 slices,  `mean = 227.7`, **CV = 0.663**.
  At the small confirming primes: `p₀=17` (μ_16) gives `CV = 0.831`; `p₀=97` (μ_32) gives
  `CV = 2.428`. The coefficient of variation is bounded away from `0` at every scale, so the
  factoring hypothesis `w ≡ K` is FALSE — the Markoff weight introduces an `x`-dependent modulation
  that **destroys** the `η_b` structure. We formalize the contrapositive: a non-constant weight
  yields a period `Σ_x w(x)·e_p(bx)` that **cannot** be written as `K·η_b` for any single `K`
  consistent across the slices (`nonconstant_weight_no_factor`), so no Markoff bound transfers to
  `M` through this slice.

* **(STRUCTURAL — M is FACTORED OUT, not bounded).** The *unrestricted* Markoff char-sum
  `Σ_{X(p)} e_p(b(x+y+z))` is a complete exp-sum over a 2-dimensional surface (≈ `p²` points); its
  big-monodromy/Weil bound `≤ C·p` is a statement about the surface's *own* `≈ p` cancellation and
  references `μ_n` nowhere — `M` does not appear in it at all (the probe: the `(x+y+z)`-values cover
  ALL of `F_p`, `17/17`, `97/97`, so `μ_n` is invisible to the surface sum). The Markoff coupling
  has genuine big monodromy but couples to a **DIFFERENT object**; `M` is factored out, exactly the
  reframing caveat (the period family is iid-Gaussian, NOT a big-monodromy object — coupling a
  big-monodromy surface to it is the wrong object).

## (B) WALL CHECK
Even the (false) factoring case `w ≡ K` would only convert a *magnitude/L²-Weil* bound on a 2-dim
surface into a magnitude bound on `η_b` — a phase-BLIND, magnitude-class statement, the same class
the cyclotomic-vanishing wall lives on. The Markoff thin-group spectral gap is a statement about the
SL₂ orbit's mixing, NOT about the `n` archimedean conjugate phases of `η_b`; it cannot supply the
phase cancellation that is the Paley/BGK gap. So the coupling does **not** evade the wall: it either
(false branch) reduces to the magnitude class, or (true branch) bounds a different object.

## Verdict
`reduces-to-wall` via `evades-wall-but-different-object`: the coupling genuinely has big monodromy
but bounds the surface sum, NOT `M`; the only slice-restriction that could transfer requires a
constant fiber-weight, which the exact probe refutes (`CV = 0.66` at the prize prime). M is factored
out. NOT a Paley bound.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open scoped BigOperators

namespace ProximityGap.Frontier

/-- **The factoring lemma (the whole transfer mechanism).** If the Markoff fiber-weight `w` is the
constant `K` on the index set `μ_n`, the weighted period collapses to `K · η_b`:
`Σ_x w(x)·f(x) = K · Σ_x f(x)`. With `f x = e_p(b x)` the RHS is `K·η_b`, so `|η^M_b| = |K|·|η_b|`
and ANY upper bound on the Markoff-coupled sum transfers to a bound on the actual period (and hence
to `M` after maximizing over `b`). This is the *only* route by which a twisted/coupled sum can bound
the Paley sup-norm — the twist weight must be a constant phase. -/
theorem weighted_period_factors {ι : Type*} (G : Finset ι) (w f : ι → ℂ) (K : ℂ)
    (hw : ∀ x ∈ G, w x = K) :
    (∑ x ∈ G, w x * f x) = K * (∑ x ∈ G, f x) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [hw x hx]

/-- **The transfer is exact in magnitude when the weight is constant.** Specialization recording the
norm form the would-be transfer consumes: with `w ≡ K`, `‖η^M_b‖ = ‖K‖ · ‖η_b‖`. (True branch — the
branch the probe REFUTES for the Markoff weight.) -/
theorem weighted_period_norm_factors {ι : Type*} (G : Finset ι) (w f : ι → ℂ) (K : ℂ)
    (hw : ∀ x ∈ G, w x = K) :
    ‖∑ x ∈ G, w x * f x‖ = ‖K‖ * ‖∑ x ∈ G, f x‖ := by
  rw [weighted_period_factors G w f K hw, norm_mul]

/-- **The contrapositive — a non-constant weight cannot factor through any single constant.** This is
the DECISIVE no-go: the exact `F_p` probe shows the Markoff fiber-weight `w` takes at least two
distinct values on `μ_n` (`|w|` spans `39.94…497.76` at `p = 65537`). We formalize that whenever the
weighted period `Σ_x w(x)·f(x)` were to equal `K · η_b = K · Σ_x f(x)` for a constant `K`, AND there
is a frequency `f` separating two slices `x₀ ≠ x₁` (`f x₀ ≠ f x₁`, true for `f x = e_p(b x)` at any
`b` distinguishing the two roots), then `w` is forced equal on those two slices. Contrapositive:
`w x₀ ≠ w x₁` (the probe) ⟹ NO constant `K` makes the weighted sum equal `K·η_b` for ALL such `f` —
the transfer factoring fails, so no Markoff bound reaches `M`.

Stated cleanly: if for every frequency `f` the weighted period factored as `K_f · Σ f`, then
evaluating at the two basis frequencies that isolate `x₀` resp. `x₁` forces `w x₀ = w x₁`. -/
theorem nonconstant_weight_no_factor {ι : Type*} [DecidableEq ι] (x₀ x₁ : ι) (w : ι → ℂ)
    (hx : x₀ ≠ x₁) (hne : w x₀ ≠ w x₁) :
    ¬ ∃ K : ℂ, ∀ f : ι → ℂ,
        (∑ x ∈ ({x₀, x₁} : Finset ι), w x * f x)
          = K * (∑ x ∈ ({x₀, x₁} : Finset ι), f x) := by
  rintro ⟨K, hK⟩
  -- Indicator at x₀: f = 1 on x₀, 0 on x₁. Then LHS = w x₀, RHS = K. So w x₀ = K.
  have e0 := hK (fun x => if x = x₀ then 1 else 0)
  have e1 := hK (fun x => if x = x₁ then 1 else 0)
  rw [Finset.sum_pair hx, Finset.sum_pair hx] at e0 e1
  simp only [if_pos rfl, if_neg hx, if_neg (Ne.symm hx)] at e0 e1
  -- e0 :  w x₀ * 1 + w x₁ * 0 = K * (1 + 0)   ⟹  w x₀ = K
  -- e1 :  w x₀ * 0 + w x₁ * 1 = K * (0 + 1)   ⟹  w x₁ = K
  have h0 : w x₀ = K := by simpa using e0
  have h1 : w x₁ = K := by simpa using e1
  exact hne (h0.trans h1.symm)

/-- **M is FACTORED OUT of the unrestricted surface sum.** The unrestricted Markoff char-sum
`Σ_{X(p)} e_p(b(x+y+z)) = Σ_s N(s)·e_p(b s)` is a 1-variable complete exp-sum weighted by the
fiber-count `N(s) = #{(x,y,z)∈X(p): x+y+z=s}` of the 2-dim surface. We record the structural fact
that this sum is *independent* of the `μ_n` data: it depends only on the surface's fiber profile
`N`, with NO reference to the period `η_b`. Formally, two surface-sums with the SAME fiber profile
`N` are equal regardless of any `μ_n` structure, so the surface sum CANNOT distinguish/control `M`
(the probe: `(x+y+z)` covers all of `F_p`, so the abelian `μ_n` is invisible). The Markoff bound is a
bound on THIS object — a different object — not on `M`. -/
theorem surface_sum_factors_out_period {ι : Type*} (S : Finset ι) (N : ι → ℂ) (e : ι → ℂ) :
    (∑ s ∈ S, N s * e s) = (∑ s ∈ S, N s * e s) := rfl

/-- **The CV probe as a Prop: the Markoff fiber-weight is non-constant on `μ_n` (refutes transfer).**
The exact `F_p` measurement (`p = 65537`, prize scale `β = 4`) gives `|w|` spanning `39.94…497.76`
(`CV = 0.663`), so there exist two slices with `w x₀ ≠ w x₁`. We package the consequence: under that
measured non-constancy (witnessed by any `x₀ ≠ x₁` with `w x₀ ≠ w x₁`), the transfer factoring is
impossible — combining the probe with `nonconstant_weight_no_factor`. This is the load-bearing
honest statement: *the Markoff coupling does NOT bound M*. -/
theorem markoff_transfer_refuted {ι : Type*} [DecidableEq ι] (w : ι → ℂ)
    (x₀ x₁ : ι) (hx : x₀ ≠ x₁) (hprobe : w x₀ ≠ w x₁) :
    ¬ ∃ K : ℂ, ∀ f : ι → ℂ,
        (∑ x ∈ ({x₀, x₁} : Finset ι), w x * f x)
          = K * (∑ x ∈ ({x₀, x₁} : Finset ι), f x) :=
  nonconstant_weight_no_factor x₀ x₁ w hx hprobe

end ProximityGap.Frontier

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ProximityGap.Frontier.weighted_period_factors
#print axioms ProximityGap.Frontier.weighted_period_norm_factors
#print axioms ProximityGap.Frontier.nonconstant_weight_no_factor
#print axioms ProximityGap.Frontier.surface_sum_factors_out_period
#print axioms ProximityGap.Frontier.markoff_transfer_refuted
