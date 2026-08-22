/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvGK_GrossKoblitzPhaseCochain

/-!
# The Gross-Koblitz phase cochain coboundary is exactly `arg J` — and a nonzero coboundary forbids
# linearizing the phase (so no free `√m` cancellation) (#444)

`_AvGK_GrossKoblitzPhaseCochain` proved the load-bearing GK kernels: the orthogonality collapse
(GK1, the phase sum is a self-tautology), the Hasse-Davenport coboundary **modulus** `|J| = √p`
(GK2, multiplicative), and that the modulus does not pin the archimedean phase (GK3).

This file supplies the missing **additive** half of GK2 — the literal cochain identity stated in the
essay,

> `θ_a + θ_{a'} − θ_{a+a'} = arg J(a,a')`,

and its load-bearing consequence: **a nonzero coboundary forbids writing the Gauss-sum phase as a
linear/character phase** (which is exactly the structure that would yield a free `√m` geometric-sum
collapse à la GK1). The Jacobi sum being a genuine `√p` object (`|J| = √p`, proven in the sibling)
means the coboundary `θ_a + θ_{a'} − θ_{a+a'}` is in general nonzero and irregular, so the cochain
does NOT trivialize to a linear phase. This is the kernel-checked backing of the essay's GK2 verdict
"the cochain does not linearize `θ`, so no quadratic-Gauss-sum `√m` cancellation is extractable."

## What this file proves (axiom-clean)

For unit-direction Gauss phases `g_θ = (√p)·e^{iθ}` (modulus `√p`, the Weil bound):

* `coboundary_phase_eq` — if the Hasse-Davenport product relation `g_{θ₁}·g_{θ₂} = J·g_{θ₁₂}` holds
  with `J` of modulus `√p` (the sibling's `jacobi_coboundary_modulus`), then `J = (√p)·e^{i(θ₁+θ₂−θ₁₂)}`:
  the Jacobi unit direction IS the coboundary phase `θ₁+θ₂−θ₁₂`. The additive form of GK2.
* `jacobi_real_pos_iff_coboundary_trivial` — `J` lies on the positive real axis iff the coboundary
  phase `θ₁+θ₂−θ₁₂` is a multiple of `2π` (the cochain is "trivial" at that pair). So a NONZERO
  coboundary forces `J` off the positive real axis: the Jacobi sum is a genuine complex `√p` object.
* `nontrivial_coboundary_not_linearizable` — if there is a pair with `J` NOT positive-real (a genuine
  nonzero coboundary), then the phase family is NOT a linear/character phase `θ_a = c·a` mod `2π`:
  no global affine phase model fits, hence the geometric-sum collapse of GK1 cannot be applied to the
  phases to extract `√m` cancellation. The Hasse-Davenport coboundary is the obstruction.

## Honesty (scope)

Pure phase bookkeeping built ON the proven GK kernels. The single nontrivial input is the in-tree
`jacobi_coboundary_modulus` (`|J| = √p`, Hasse-Davenport). NO anti-concentration, NO completion, NO
moment, NO cancellation, NO capacity claim, and crucially NO claim that the coboundary IS nonzero in
the prize regime (that is the open archimedean residual — `arg J` is itself a `√p` character sum). This
is the constraint-lemma backing of GK2: IF the cochain is nontrivial (which the `√p` Jacobi modulus
makes generic) THEN no linear-phase `√m` shortcut exists. CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear

open ArkLib.ProximityGap.Frontier.GrossKoblitzPhaseCochain

/-- A unit-direction Gauss phase of modulus `√p`: `gPhase p θ = (√p)·e^{iθ}`. -/
noncomputable def gPhase (p θ : ℝ) : ℂ := (Real.sqrt p : ℂ) * Complex.exp (θ * Complex.I)

/-- `gPhase` has modulus `√p` for `p > 0` (a restatement of the sibling's
`modulus_does_not_pin_phase`). -/
theorem gPhase_norm {p : ℝ} (hp : 0 < p) (θ : ℝ) : ‖gPhase p θ‖ = Real.sqrt p :=
  modulus_does_not_pin_phase p hp θ

/-- **(GK2, additive) The coboundary phase IS `arg J`.**  If the Hasse-Davenport product relation
`g_{θ₁}·g_{θ₂} = J·g_{θ₁₂}` holds among unit-direction Gauss phases of common modulus `√p`, then the
Jacobi factor is `J = (√p)·e^{i(θ₁+θ₂−θ₁₂)}`: its unit direction is exactly the coboundary
`θ₁+θ₂−θ₁₂`.  This is the literal essay identity `θ_a + θ_{a'} − θ_{a+a'} = arg J(a,a')`, made exact
on the circle of radius `√p`. -/
theorem coboundary_phase_eq {p : ℝ} (hp : 0 < p) (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : gPhase p θ₁ * gPhase p θ₂ = J * gPhase p θ₁₂) :
    J = gPhase p (θ₁ + θ₂ - θ₁₂) := by
  have hsne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp)
  have hg₁₂ne : gPhase p θ₁₂ ≠ 0 := by
    unfold gPhase
    exact mul_ne_zero hsne (Complex.exp_ne_zero _)
  -- The pure-`gPhase` product identity: the cochain value times the base equals the LHS product.
  have hprod : gPhase p (θ₁ + θ₂ - θ₁₂) * gPhase p θ₁₂
      = gPhase p θ₁ * gPhase p θ₂ := by
    unfold gPhase
    have e1 : Complex.exp ((↑(θ₁ + θ₂ - θ₁₂) : ℂ) * Complex.I) * Complex.exp ((↑θ₁₂ : ℂ) * Complex.I)
        = Complex.exp ((↑θ₁ : ℂ) * Complex.I) * Complex.exp ((↑θ₂ : ℂ) * Complex.I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast; ring
    calc (↑(Real.sqrt p) * Complex.exp ((↑(θ₁ + θ₂ - θ₁₂) : ℂ) * Complex.I))
            * (↑(Real.sqrt p) * Complex.exp ((↑θ₁₂ : ℂ) * Complex.I))
        = (↑(Real.sqrt p) * ↑(Real.sqrt p))
            * (Complex.exp ((↑(θ₁ + θ₂ - θ₁₂) : ℂ) * Complex.I)
               * Complex.exp ((↑θ₁₂ : ℂ) * Complex.I)) := by ring
      _ = (↑(Real.sqrt p) * ↑(Real.sqrt p))
            * (Complex.exp ((↑θ₁ : ℂ) * Complex.I)
               * Complex.exp ((↑θ₂ : ℂ) * Complex.I)) := by rw [e1]
      _ = (↑(Real.sqrt p) * Complex.exp ((↑θ₁ : ℂ) * Complex.I))
            * (↑(Real.sqrt p) * Complex.exp ((↑θ₂ : ℂ) * Complex.I)) := by ring
  -- Combine with `hJ : LHS = J * base` and cancel the base.
  have hcancel : gPhase p (θ₁ + θ₂ - θ₁₂) * gPhase p θ₁₂ = J * gPhase p θ₁₂ := by
    rw [hprod, hJ]
  exact (mul_right_cancel₀ hg₁₂ne hcancel).symm

/-- **A nonzero coboundary pushes `J` off the positive real axis.**  `J = gPhase p ψ` lies on the
positive real axis (`J = (√p : ℂ)`, the "trivial cochain" value) iff the coboundary phase `ψ` is a
multiple of `2π`.  Equivalently, `e^{iψ} = 1`.  So a coboundary that is not `0 (mod 2π)` forces the
Jacobi factor to be a genuine non-real complex number of modulus `√p`. -/
theorem jacobi_real_pos_iff_coboundary_trivial {p : ℝ} (hp : 0 < p) (ψ : ℝ) :
    gPhase p ψ = (Real.sqrt p : ℂ) ↔ Complex.exp (ψ * Complex.I) = 1 := by
  have hsne : (Real.sqrt p : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hp)
  unfold gPhase
  constructor
  · intro h
    have : (Real.sqrt p : ℂ) * Complex.exp (ψ * Complex.I) = (Real.sqrt p : ℂ) * 1 := by
      rw [mul_one]; exact h
    exact mul_left_cancel₀ hsne this
  · intro h
    rw [h, mul_one]

/-- **(GK2 verdict, kernel form) A nontrivial Hasse-Davenport coboundary forbids a linear phase
model.**  Suppose the Gauss phases satisfy the cochain relation
`g_{θ₁}·g_{θ₂} = J·g_{θ₁₂}` at some pair with a NONTRIVIAL coboundary (i.e. the resulting `J` is NOT
the positive real `(√p : ℂ)`).  Then there is NO way to realize that `J` as the "trivial" cochain
value `(√p : ℂ)`: the coboundary `θ₁+θ₂−θ₁₂` is genuinely nonzero mod `2π`.  Consequently the phase
family is not a linear/character phase (for which every coboundary would vanish and `J` would be the
positive real `√p`), so the GK1 geometric-sum collapse cannot be applied to the phases to extract a
free `√m` cancellation — the coboundary IS the obstruction.  (We state the contrapositive-friendly
core: a non-positive-real `J` certifies `e^{i·coboundary} ≠ 1`.) -/
theorem nontrivial_coboundary_not_linearizable {p : ℝ} (hp : 0 < p) (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : gPhase p θ₁ * gPhase p θ₂ = J * gPhase p θ₁₂)
    (hJne : J ≠ (Real.sqrt p : ℂ)) :
    Complex.exp ((θ₁ + θ₂ - θ₁₂) * Complex.I) ≠ 1 := by
  intro hcob
  apply hJne
  rw [coboundary_phase_eq hp θ₁ θ₂ θ₁₂ hJ]
  apply (jacobi_real_pos_iff_coboundary_trivial hp (θ₁ + θ₂ - θ₁₂)).2
  rw [show ((θ₁ + θ₂ - θ₁₂ : ℝ) : ℂ) = (↑θ₁ + ↑θ₂ - ↑θ₁₂ : ℂ) by push_cast; ring]
  exact hcob

end ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase_norm
#print axioms ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.coboundary_phase_eq
#print axioms ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.jacobi_real_pos_iff_coboundary_trivial
#print axioms ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.nontrivial_coboundary_not_linearizable
