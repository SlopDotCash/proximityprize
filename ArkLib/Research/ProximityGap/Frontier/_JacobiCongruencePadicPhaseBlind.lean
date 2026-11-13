/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Jacobi/Gauss congruence theory (p-adic valuations, mod `p^k` lifting) is PHASE-BLIND on F2

**Method tested:** congruence theory for Jacobi sums via `p`-adic valuations and mod `p^k`
lifting (arXiv:2510.13924, "Simpler congruences for Jacobi sum `J(1,1)_49` of order 49";
generally the Stickelberger / Gross–Koblitz `p`-adic valuation of Gauss sums and their
congruences mod `(1−ζ)^k`).

**Face attacked:** F2 / Energy — `A_r = Σ_{b≠0} ‖η_b‖^{2r} ≤ (q−1)·Wick_r`, the additive
`2r`-energy of `μ_n`, equivalently `M = max_{b≠0}‖η_b‖`.

**The exact bridge (verified numerically, `probe_jacobi_eta`, n=16, p∈{97,193,257,641,65537}):**
with `Q = (p−1)/n`,
`  η_b = (n/(p−1))·( −1 + Σ_{t=1}^{Q−1} χ̄_{nt}(b)·g(χ_{nt}) )`,
so `η_b` is a normalized sum of `Q−1 ≈ p/n` **Gauss sums**, each of **archimedean magnitude
`√p`**. The energy `A_r` is the archimedean magnitude of a sum of `~Q^{2r}` Gauss-sum products
surviving the additive-energy constraint `Σt ≡ Σs (mod Q)`. The prize needs `√`-cancellation
among the **complex phases** of these products.

**The Stickelberger machinery (the paper's content):** gives the EXACT `p`-adic valuation
`v_π(g(χ_{nt})) = ⟨−nt/(p−1)⟩` of each Gauss sum (and, by mod-`p^k` lifting, congruences for
their products). Numerically (`probe_stickelberger`, `probe_jacobi_eta`) at every scale tested:
* the valuations are **genuinely distinct** across the `Q−1` factors (full Stickelberger spread
  in `(0,1)`) — so the method DOES refine, along the non-archimedean axis;
* but **every Gauss sum has the SAME archimedean magnitude `√p`** (all valuations lie strictly
  in `(0,1)`), and within a single fixed `p`-adic-valuation class the surviving products still
  **cancel archimedean by up to 99%** (`probe_phase_blind`, p=193).

**The exact failing step (this file formalizes it).** A `p`-adic valuation is a *non-archimedean*
absolute value: it is invariant under multiplication by an archimedean unit (a root of unity / any
unit-modulus complex scalar) and on a sum it only sees the *minimum* valuation, never archimedean
phase cancellation. Hence the entire Stickelberger / mod-`p^k` congruence content is **orthogonal**
to the archimedean `√`-cancellation the F2 face requires: it cannot separate an aligned (large
`‖·‖`) configuration of Gauss-sum products from a cancelling (small `‖·‖`) one when they have the
same valuation data. This is the precise, abstract reason the method reduces to the wall — it is the
phase-blindness obstruction (memory `issue444-bsum-dichotomy-formalized`) instantiated for the
congruence/`p`-adic refinement specifically.

We model a "`p`-adic valuation / congruence functional" abstractly as any functional `v` on the
pieces that is **invariant under unit-modulus rescaling** of each piece (the defining property
of a non-archimedean absolute value applied to archimedean-phase changes). The theorems show such a
`v` is constant along a whole circle of archimedean reconfigurations whose archimedean norms range
from `0` (full cancellation) to the triangle-inequality maximum.

No prize closure is claimed. These are exact bookkeeping lemmas isolating WHY congruence theory
does not bind the F2 energy.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind

open scoped Complex

/-! ## The model: pieces of equal archimedean magnitude (Gauss sums, `‖g‖ = √p`). -/

/-- A finite family of complex pieces `A : ι → ℂ` is **equimagnitude `ρ`** if every piece has
norm exactly `ρ`.  Models the Gauss-sum factors `g(χ_{nt})`, all of archimedean magnitude `√p`. -/
def Equimagnitude {ι : Type*} (s : Finset ι) (A : ι → ℂ) (ρ : ℝ) : Prop :=
  ∀ i ∈ s, ‖A i‖ = ρ

/-- A **phase-blind functional** on the family: a real-valued readout `v` of the pieces that is
invariant under replacing each piece `A i` by `c i • A i` for any unit-modulus `c i` (i.e. `c i`
on the unit circle).  Every `p`-adic valuation / mod-`p^k` congruence readout has this property,
because a root of unity (or any archimedean unit) is a `p`-adic unit: it does not change the
`π`-adic valuation.  This is the *defining* non-archimedean feature we exploit. -/
def PhaseBlind {ι : Type*} (s : Finset ι) (v : (ι → ℂ) → ℝ) : Prop :=
  ∀ (A : ι → ℂ) (c : ι → Circle), v (fun i => (c i : ℂ) * A i) = v A

/-! ## Archimedean range: equimagnitude families span norm `[0, ρ·#s]`. -/

/-- An all-aligned equimagnitude family (every piece equal to `ρ`, a positive real) has
archimedean norm exactly `ρ·#s` — the triangle-inequality MAXIMUM. -/
theorem norm_sum_aligned {ι : Type*} (s : Finset ι) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ‖∑ _i ∈ s, (ρ : ℂ)‖ = ρ * s.card := by
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ,
    mul_comm]

/-- For an even-cardinality index set there is a SIGNED equimagnitude reconfiguration with
archimedean norm `0`: half the pieces `+ρ`, half `−ρ`, full cancellation.  Concretely, pairing
`{0,1,…,2m−1}` as `(2j, 2j+1)` and assigning `+ρ, −ρ` cancels.  We give the clean two-piece core:
`ρ + (−ρ) = 0`, the smallest nontrivial cancelling equimagnitude configuration. -/
theorem norm_sum_cancel_two (ρ : ℝ) :
    ‖(ρ : ℂ) + (-(ρ : ℂ))‖ = 0 := by
  simp

/-! ## The orthogonality theorem: a phase-blind functional cannot detect the cancellation. -/

/-- **Core obstruction (two-piece).** Take a phase-blind functional `v` on a two-element family.
The aligned configuration `(ρ, ρ)` (archimedean norm `2ρ`) and the cancelling configuration
`(ρ, −ρ)` (archimedean norm `0`) differ only by multiplying the second piece by the unit-modulus
scalar `−1`.  Therefore `v` assigns them the **same value**: the phase-blind / `p`-adic readout
cannot distinguish full archimedean cancellation from full archimedean alignment.

This is the exact failing step of the congruence method on F2: Stickelberger valuations and
mod-`p^k` congruences are phase-blind functionals of the Gauss-sum pieces, so they are constant
across the archimedean norm range `[0, 2ρ]` and never see the `√`-cancellation the energy needs. -/
theorem phaseBlind_cannot_separate_cancel_from_aligned
    (v : (Fin 2 → ℂ) → ℝ) (ρ : ℝ)
    (hv : PhaseBlind (Finset.univ : Finset (Fin 2)) v) :
    v (fun i => if i = 0 then (ρ : ℂ) else (-(ρ : ℂ)))
      = v (fun _ => (ρ : ℂ)) := by
  classical
  -- the cancelling config is `(c · aligned)` with `c 0 = 1`, `c 1 = -1` (both unit modulus).
  -- `hv aligned c : v (fun i => c i * aligned i) = v aligned`; rewrite the LHS pieces to `cancel`.
  have h := hv (fun _ => (ρ : ℂ)) (fun i => if i = 0 then (1 : Circle) else (-1 : Circle))
  refine Eq.trans ?_ h
  congr 1
  funext i
  fin_cases i <;> simp

/-- **Norm-gap form.** The phase-blind value `v` is identical on a configuration whose archimedean
norm is `0` and one whose norm is `2ρ`.  So no inequality of the form "`v(A) ≤ θ ⟹ ‖Σ A‖ small`"
can hold with any nontrivial `θ`-separation: the same `v`-value coexists with norms `0` and `2ρ`.
This is why a congruence/`p`-adic bound cannot upper-bound the F2 energy `A_r = ‖Σ products‖`. -/
theorem phaseBlind_value_compatible_with_full_norm_range
    (v : (Fin 2 → ℂ) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hv : PhaseBlind (Finset.univ : Finset (Fin 2)) v) :
    ∃ Acancel Aaligned : Fin 2 → ℂ,
      v Acancel = v Aaligned ∧
      ‖∑ i, Acancel i‖ = 0 ∧
      ‖∑ i, Aaligned i‖ = 2 * ρ := by
  refine ⟨(fun i => if i = 0 then (ρ : ℂ) else (-(ρ : ℂ))), (fun _ => (ρ : ℂ)),
    phaseBlind_cannot_separate_cancel_from_aligned v ρ hv, ?_, ?_⟩
  · -- cancelling sum: ρ + (−ρ) = 0
    rw [Fin.sum_univ_two]
    simp
  · -- aligned sum: ρ + ρ = 2ρ, norm = 2ρ since ρ > 0
    rw [Fin.sum_univ_two]
    change ‖(ρ : ℂ) + (ρ : ℂ)‖ = 2 * ρ
    rw [show ((ρ : ℂ) + (ρ : ℂ)) = ((2 * ρ : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-! ## Reduction verdict (interface form).

The two theorems above package the precise sense in which the congruence/`p`-adic method REDUCES
on F2: a phase-blind functional `v` (any Stickelberger valuation or mod-`p^k` congruence readout of
the Gauss-sum pieces) is constant across the full archimedean norm range `[0, 2ρ]` of an
equimagnitude family.  An F2 energy bound is exactly a statement `‖Σ products‖ ≤ (Wick bound)`, i.e.
control of the archimedean norm; the method only controls `v`, which is blind to that norm.

Therefore: to bind F2, one CANNOT use only valuation/congruence data of the Gauss-sum factors; one
must inject genuinely archimedean phase information about the surviving products — exactly the short
`±1`-vanishing-sum-of-`2^μ`-th-roots cancellation that is the wall.  The method is an arithmetic
refinement of *magnitude/divisibility*, not of *archimedean phase*. -/

/-- The reduction, stated as a `Prop` for downstream citation: any phase-blind functional admits an
aligned/cancel pair with identical value but maximal norm gap.  (Discharged by the theorem above for
the canonical two-piece witness.) -/
def CongruenceMethodPhaseBlindOnF2 : Prop :=
  ∀ (v : (Fin 2 → ℂ) → ℝ) (ρ : ℝ), 0 < ρ →
    PhaseBlind (Finset.univ : Finset (Fin 2)) v →
    ∃ Acancel Aaligned : Fin 2 → ℂ,
      v Acancel = v Aaligned ∧ ‖∑ i, Acancel i‖ = 0 ∧ ‖∑ i, Aaligned i‖ = 2 * ρ

theorem congruenceMethodPhaseBlindOnF2_holds : CongruenceMethodPhaseBlindOnF2 := by
  intro v ρ hρ hv
  exact phaseBlind_value_compatible_with_full_norm_range v ρ hρ hv

end ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind

#print axioms ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.norm_sum_aligned
#print axioms ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.norm_sum_cancel_two
#print axioms ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.phaseBlind_cannot_separate_cancel_from_aligned
#print axioms ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.phaseBlind_value_compatible_with_full_norm_range
#print axioms ProximityGap.Frontier.JacobiCongruencePadicPhaseBlind.congruenceMethodPhaseBlindOnF2_holds
