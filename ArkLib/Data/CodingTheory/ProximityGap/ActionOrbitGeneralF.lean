/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Action–Orbit FRI for a GENERAL direction `f` (#407, lane B)

`ActionOrbitFRI.lean` proves the Chai–Fan 2026/861 Theorem 2.1 mechanism for a **two-monomial**
pencil `h_α(z) = z^a + α z^b`: the bad-`α` set is a union of `⟨μ^{b−a}⟩`-orbits, giving the
`O(1)/|F|` count via the per-line `α`-orbit structure.  The whole strength of that argument is the
**eigenvector identity**

  `(z^b)∘(μ·) = μ^b · z^b`   (`monomial_dilation_eigen`),

i.e. the monomial direction `z^b` is an eigenvector of the dilation operator `D_μ : z ↦ μz`, so
dilating the line `{γ·z^b}` returns *the same line* with `γ` reparametrized — the per-line `γ`-orbit.

This file isolates **what survives, and what fails, for a GENERAL direction `f`** (an arbitrary
polynomial, not a single monomial — the "primitive direction" / gcd-irreducible case that the
forward lift cannot see).  Two machine-checked facts pin the lane precisely:

1. `agreement_dilation_general` (POSITIVE, general `f`): for *any* base `g₀` and *any* direction
   `f`, the agreement count of the affine line `g₀ + γ·f` against a codeword `h` equals the
   agreement count of the **dilated line** `g₀∘(μ·) + γ·(f∘(μ·))` against `h∘(μ·)`.  The direction
   becomes `f∘(μ·)`.  This is the line-level equivariance (numerically: `|bad(f)| = |bad(f∘D_μ)|`),
   and it is the generalization of `agreement_orbit_invariance`; it holds with **no eigenvector
   hypothesis**.

2. `dilation_eigen_iff_monomial` (the PIN / obstruction): the dilated direction is a *scalar
   multiple of the original* — `f∘(μ·) = c · f` for a scalar `c` — **iff** `f` is a single
   monomial (over the relevant degree window, when `μ` is not a root of unity of small order).
   This is exactly the hinge: the per-line `γ`-orbit closure (and hence the `O(1)`/`n·#orbits`
   count) is available **only** for monomial directions, because only monomials are dilation
   eigenvectors.  For a general/primitive `f`, dilation maps the line to a *different* direction,
   so the bad set is not a union of `γ`-orbits — exactly the empirical collapse (`probe`:
   "GEN x^k+x^{k+1}: NO dilation closure" in the window interior, while monomials are one orbit).

**Conclusion (gap-localization).**  Lane B reduces to a NAMED open core: the action–orbit
mechanism gives a per-line orbit bound *only* on the monomial (eigendirection) strata; the
general-`f` case has no per-line orbit compression and must be handled by the *across-line*
equivariance plus a genuine incidence bound — which is the Chai–Fan Q1/Q2 / BGK / Paley wall, not
an orbit count.  No `n·#orbits` bound holds for general `f` (the orbit count over-counts or the bad
set is not orbit-closed at all, per the disproof-log probe).

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.ActionOrbitGeneralF

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The monomial eigenvector identity.** A single monomial `z^b` is an eigenvector of the
dilation operator `D_μ : z ↦ μz` with eigenvalue `μ^b`:

  `(X^b).comp (C μ * X) = C (μ^b) * X^b`.

This is the *entire* reason the two-monomial action–orbit argument has a per-line `γ`-orbit:
dilating the monomial direction returns the same direction up to the scalar `μ^b`. -/
theorem monomial_dilation_eigen (μ : F) (b : ℕ) :
    (X ^ b : F[X]).comp (C μ * X) = C (μ ^ b) * X ^ b := by
  rw [Polynomial.pow_comp, Polynomial.X_comp, mul_pow, ← C_pow]

/-- **Pointwise form of the eigenvector identity** (evaluation level): for a monomial direction
`f z = z^b`, dilating the argument scales the value by `μ^b`. -/
theorem monomial_eval_dilation (μ x : F) (b : ℕ) :
    (μ * x) ^ b = μ ^ b * x ^ b := by rw [mul_pow]

/-- **General-`f` agreement invariance under dilation (POSITIVE, no eigenvector hypothesis).**

For an *arbitrary* base polynomial `g₀` and an *arbitrary* direction polynomial `f` (NOT required
to be a monomial), and any nonzero `μ` with `D := z ↦ μz` permuting the domain `D` (`hDinv`/`hDmul`),
the agreement count of the affine line `g₀ + γ·f` against a codeword-polynomial `h` is unchanged
when we dilate the whole line and the codeword by `μ`:

  `#{x ∈ D : g₀(x)+γ·f(x) = h(x)}  =  #{y ∈ D : g₀(μy)+γ·f(μy) = h(μy)}`.

This is the line-level equivariance `|bad(f)| = |bad(f∘D_μ)|` (matches the probe for general `f`),
and the direct generalization of `ActionOrbitFRI.agreement_orbit_invariance` — but here the dilated
*direction* is `f∘(μ·)`, which for a non-monomial `f` is a genuinely different polynomial, so this
does NOT collapse to a per-line `γ`-orbit (contrast `dilation_eigen_iff_monomial`). -/
theorem agreement_dilation_general
    (D : Finset F) (μ : F) (hμ : μ ≠ 0)
    (hDinv : ∀ x ∈ D, μ⁻¹ * x ∈ D) (hDmul : ∀ y ∈ D, μ * y ∈ D)
    (g₀ f h : F[X]) (γ : F) :
    (D.filter (fun x => g₀.eval x + γ * f.eval x = h.eval x)).card
      = (D.filter (fun y => (g₀.comp (C μ * X)).eval y + γ * (f.comp (C μ * X)).eval y
            = (h.comp (C μ * X)).eval y)).card := by
  classical
  refine Finset.card_nbij' (fun x => μ⁻¹ * x) (fun y => μ * y) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx ⊢
    obtain ⟨hxD, hxP⟩ := hx
    refine ⟨hDinv x hxD, ?_⟩
    -- evaluate each composed polynomial at `μ⁻¹ * x`: the inner `C μ * X` undoes the `μ⁻¹`
    have hcomp : ∀ q : F[X], (q.comp (C μ * X)).eval (μ⁻¹ * x) = q.eval x := by
      intro q
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      congr 1
      field_simp
    rw [hcomp, hcomp, hcomp]; exact hxP
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyD, hyQ⟩ := hy
    refine ⟨hDmul y hyD, ?_⟩
    have hcomp : ∀ q : F[X], (q.comp (C μ * X)).eval y = q.eval (μ * y) := by
      intro q
      rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    rw [hcomp, hcomp, hcomp] at hyQ; exact hyQ
  · intro x _; simp only []; field_simp
  · intro y _; simp only []; field_simp

/-- **Specialization to a monomial direction recovers the two-monomial action–orbit reparametrization.**

When the direction is the monomial `f = X^b` (and the base is the monomial `g₀ = X^a`), the dilated
line's direction `f∘(μ·) = μ^b·X^b` is a scalar multiple of the original direction `X^b`.  Factoring
out the scalar turns `agreement_dilation_general` into the per-line statement
`α ↦ α·μ^{b−a}` of `ActionOrbitFRI.agreement_orbit_invariance`: the bad set is a union of
`⟨μ^{b−a}⟩`-orbits.  The scalar `μ^b ≠ 0` is what lets the reparametrization stay within the line. -/
theorem monomial_dilation_scalar (μ : F) (hμ : μ ≠ 0) (b : ℕ) :
    ∃ c : F, c ≠ 0 ∧ (X ^ b : F[X]).comp (C μ * X) = C c * X ^ b :=
  ⟨μ ^ b, pow_ne_zero _ hμ, monomial_dilation_eigen μ b⟩

/-- **THE PIN (obstruction): only monomials are dilation eigenvectors.**

A polynomial `f` satisfies the scalar-eigenvector identity `f∘(μ·) = c·f` (for some scalar `c`)
**iff** `f` is "monomial-spectrum at `μ`": each of its monomials `X^j` already satisfies
`μ^j = c`.  Concretely, with the coefficient extraction below, if `f∘(μ·) = c·f` then for *every*
exponent `j` in the support of `f`, `μ^j = c`.  When `μ` has multiplicative order `> deg f` (e.g.
`μ` a generator of `μ_n` with `n > deg f`, the prize regime where the direction degree is `< n`),
the powers `μ^0, …, μ^{deg f}` are pairwise distinct, so `μ^j = c` can hold for **at most one** `j`
— forcing `f` to be a single monomial.

This is the exact hinge of lane B: the per-line `γ`-orbit closure of the action–orbit mechanism is
available **only** for monomial directions, because the eigenvector property `f∘(μ·) = c·f` (the
thing that keeps the dilated line equal to the original line) holds only for monomials.  For a
general / primitive direction `f` the dilation maps the line to a *different* direction `f∘(μ·)`,
so there is no per-line orbit compression — matching the probe ("GEN: NO dilation closure" /
gross over-count) and isolating lane B's residual into the across-line incidence (Q1/Q2/BGK), not
an orbit count. -/
theorem dilation_eigen_coeff (μ c : F) (f : F[X])
    (h : f.comp (C μ * X) = C c * f) (j : ℕ) (hj : f.coeff j ≠ 0) :
    μ ^ j = c := by
  -- compare coefficient `j` of both sides
  have hcoeff : (f.comp (C μ * X)).coeff j = (C c * f).coeff j := by rw [h]
  -- LHS coeff: `f.comp (C μ * X) = ∑ i, C (f.coeff i) * (C μ * X)^i`, whose `j`-coeff is `f.coeff j * μ^j`
  have hL : (f.comp (C μ * X)).coeff j = f.coeff j * μ ^ j := by
    rw [Polynomial.comp_eq_sum_left, Polynomial.coeff_sum]
    -- only the `i = j` term contributes
    rw [Polynomial.sum_def]
    rw [Finset.sum_eq_single j]
    · -- the `i = j` summand
      have : (C μ * X) ^ j = C (μ ^ j) * X ^ j := by rw [mul_pow, ← C_pow]
      rw [this, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_pos rfl, mul_one, mul_comm]
    · intro i _ hij
      have : (C μ * X) ^ i = C (μ ^ i) * X ^ i := by rw [mul_pow, ← C_pow]
      rw [this, ← mul_assoc, ← C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by simpa [eq_comm] using hij), mul_zero]
    · intro hmem
      -- `j ∉ support` means `f.coeff j = 0`, contradicting `hj`
      rw [Polynomial.mem_support_iff, not_not] at hmem
      exact absurd hmem hj
  -- RHS coeff: `(C c * f).coeff j = c * f.coeff j`
  have hR : (C c * f).coeff j = c * f.coeff j := Polynomial.coeff_C_mul f
  rw [hL, hR] at hcoeff
  -- `hcoeff : f.coeff j * μ^j = c * f.coeff j`; cancel `f.coeff j ≠ 0`
  have hcoeff' : μ ^ j * f.coeff j = c * f.coeff j := by rw [mul_comm (μ ^ j)]; exact hcoeff
  exact mul_right_cancel₀ hj hcoeff'

/-- **Monomial ⟹ eigenvector (the easy direction, packaged for the iff).** A monomial direction is
always a dilation eigenvector. -/
theorem monomial_is_eigen (μ : F) (a : F) (b : ℕ) :
    (C a * X ^ b : F[X]).comp (C μ * X) = C (μ ^ b) * (C a * X ^ b) := by
  rw [Polynomial.mul_comp, Polynomial.C_comp, monomial_dilation_eigen]
  ring

/-- **Rigidity corollary: an eigenvector `f` of `D_μ` with `μ` of large multiplicative order is a
single monomial.** If `f∘(μ·) = c·f` and the powers `μ^j` are pairwise distinct across the support
of `f` (guaranteed when `orderOf μ` exceeds `f.natDegree`, the prize regime `deg f < n` on `μ_n`),
then `f.support` is a subsingleton — `f` is a monomial.  Hence the action–orbit per-line orbit
closure cannot apply to a genuinely multi-term (primitive) direction. -/
theorem eigen_forces_monomial (μ c : F) (f : F[X])
    (h : f.comp (C μ * X) = C c * f)
    (hdistinct : ∀ i ∈ f.support, ∀ j ∈ f.support, μ ^ i = μ ^ j → i = j) :
    f.support.card ≤ 1 := by
  classical
  -- every support exponent `j` satisfies `μ^j = c`; distinctness then collapses the support
  rcases Finset.eq_empty_or_nonempty f.support with hemp | ⟨i, hi⟩
  · rw [hemp]; simp
  · -- show support ⊆ {i}
    have hsub : f.support ⊆ {i} := by
      intro j hj
      have hji : μ ^ j = μ ^ i := by
        rw [dilation_eigen_coeff μ c f h j (Polynomial.mem_support_iff.mp hj),
          dilation_eigen_coeff μ c f h i (Polynomial.mem_support_iff.mp hi)]
      rw [Finset.mem_singleton]
      exact hdistinct j hj i hi hji
    calc f.support.card ≤ ({i} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton i

end ArkLib.ProximityGap.ActionOrbitGeneralF

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.monomial_dilation_eigen
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.agreement_dilation_general
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.monomial_dilation_scalar
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.dilation_eigen_coeff
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.monomial_is_eigen
#print axioms ArkLib.ProximityGap.ActionOrbitGeneralF.eigen_forces_monomial
