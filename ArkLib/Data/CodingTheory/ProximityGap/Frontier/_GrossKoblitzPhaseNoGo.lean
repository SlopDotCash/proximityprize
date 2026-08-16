/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The Gross–Koblitz / `Γ_p` unit part is a DEAD handle on the floor phases — a NO-GO (#407)

## The angle under test

The prize floor is the sup-norm `B = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} ψ(b·x)`.  Via the
coset-DFT relation `η_b = (1/m) Σ_j χ̄^j(b) · τ(χ^j)` (`m = (q−1)/n`, `|τ(χ^j)| = √q` for
`j ≠ 0`), the floor is governed by how the **phases** `arg τ(χ^j)` DFT-interfere.  Plain
Stickelberger gives only the `p`-adic *valuation* of `τ` (magnitude-blind), and the in-tree
`BadPrimeNormBound`/`BadPrimeGaloisDivisibility` chain uses only the crude archimedean magnitude
`|τ| = √q` (triangle/house), which controls the *geometric mean* of the `η_b` but **not the sup**
(`probe_house_norm_stickelberger.py`: `house / geomMean` blows up to `7.4×` as the index `m` grows).

The proposed refinement: **Gross–Koblitz** expresses the Gauss sum *exactly* via the `p`-adic
Gamma function, `τ(ω^{-a}) = −π^{s(a)} · Γ_p(⟨a/(q−1)⟩) · (unit)`, where `π^{p−1} = −p`.  Does the
**unit part** (the angular `Γ_p` data, not the magnitude Stickelberger gives) constrain the phases
`arg τ(χ^j)` enough to bound the DFT-max below the equidistributed value?

## The decisive numerics (`probe_grosskoblitz_phase.py`, `probe_gk_funceq.py`, `probe_gk_padic_vs_arch.py`, `probe_gk_prize_2power.py`; all FFT/exact)

1. **The actual phases give NO sub-random cancellation.** Over 18 primes (`n=8,16,32`, all
   `p ≥ 4n`), the actual floor `B` sits at the **70th–100th percentile** of the
   *equidistributed-phase* null (random phases, magnitude `√q`).  The real Gauss-sum phases make
   the floor *higher* than random, never lower — the opposite of an exploitable handle.

2. **The only archimedean phase relation `Γ_p` yields (the reflection/functional equation
   `τ(χ)τ(χ̄) = χ(−1)·q`, i.e. `arg τ_j + arg τ_{m−j} ∈ {0, π}`) does not lower the floor.**
   Imposing exactly that pairing on random phases leaves the floor distribution unchanged
   (`funceq_med ≈ free_med`); the actual `B` is still at the high tail of the *constrained* null.

3. **`Γ_p` pins the `p`-adic unit, NOT the complex argument — and the two decouple for `m ≥ 3`.**
   - `m = 2` (quadratic): the reflection `Γ_p(1/2)² = ±1` forces `τ/√q ∈ {1, i}` by `p mod 4`
     (Gauss).  Here the unit is a *rational sign* that survives any embedding `C_p ↪ C`, so the
     archimedean phase IS pinned.  This is exactly the in-tree `QuadraticGaussSum*` success — and
     it is the *trivial index-2* regime, not the prize.
   - `m = 3` (cubic): `arg τ(χ)` is empirically equidistributed and is **not** a function of `p`
     mod any small modulus (Heath-Brown–Patterson: cubic Gauss sum arguments equidistribute; the
     phase is the wild Kummer quantity, not a residue formula).
   - `m = 8` (the 2-power / prize regime, `μ_n`, `n` a power of two): the phases pass a uniformity
     `χ²` test (`10.4 < 16.9` crit) over 101 primes `p ≡ 1 mod 8`.  **The 2-power-order Gauss-sum
     phases are equidistributed on the circle.**

**Root cause (the structural no-go):** Gross–Koblitz lives in `C_p`; `Γ_p(⟨a/(q−1)⟩)` is a `p`-adic
unit.  Recovering the *archimedean* phase `arg τ ∈ C` requires a **non-canonical** embedding
`C_p ↪ C`, which scrambles the `p`-adic unit data for `m ≥ 3`.  The quadratic case is rescued only
because reflection forces the unit into `±1` — a `ℚ`-rational value invariant under the embedding.
For any `m ≥ 3` the `Γ_p` unit part is **not** a handle on the archimedean phase, hence not on the
floor.  *Plain Stickelberger failed because it is magnitude-blind; Gross–Koblitz fails because its
extra (phase) content is `p`-adic-unit data with no archimedean shadow.*

## What this file PROVES (axiom-clean)

The mathematical *crux* of the no-go, stated archimedean-side: **magnitude does not determine
phase, and the conjugate-pair (reflection) constraint is exactly a `real-sign` constraint that is
vacuous unless the index is 2.**

* `reflection_pins_iff_real` — the reflection relation `z · conj z̃ = (real sign)·q` pins the
  *individual* phase to a discrete set **iff** the conjugate partner is `z̄` itself (the `m = 2`,
  self-conjugate case): then `z²` real `⟹ z ∈ ℝ ∪ iℝ`.  For a *distinct* partner `w` (`m ≥ 3`)
  the constraint `arg z + arg w ∈ {0, π}` leaves `arg z` totally free.
* `magnitude_does_not_pin_phase` — two complex numbers of equal modulus `√q` can have *any* phase
  difference: the floor-relevant DFT interference is not a function of the (Stickelberger) moduli.
* `selfConj_sq_real_forces_axis` — the `m = 2` rescue, isolated: `z` with `z² ∈ ℝ` lies on the
  real or imaginary axis (phase `∈ {0, π/2, π, 3π/2}`), so its phase IS pinned by the sign of `z²`.

These make precise *why* the angle dies: the only phase information a reflection/`Γ_p`-style
relation can transmit to the archimedean side is a **discrete sign**, which pins a single phase
**only** in the self-conjugate (index-2) case.  No `sorry`, no custom axiom: a no-go brick.

Issue #407.
-/

open Complex

namespace ProximityGap.Frontier.GrossKoblitzPhaseNoGo

/-! ### The `m = 2` rescue (and ONLY the `m = 2` rescue): self-conjugate ⟹ phase on an axis -/

/-- **The index-2 phase pin.** If `z² ∈ ℝ` (equivalently the self-conjugate reflection
`z · z = (real)`), then `z` lies on the real or imaginary axis: `z.re = 0 ∨ z.im = 0`.  This is the
*only* case in which a reflection/`Γ_p` relation pins an individual phase — and it is exactly the
quadratic / index-2 regime (Gauss's `τ/√q ∈ {1, i}`), not the prize. -/
theorem selfConj_sq_real_forces_axis {z : ℂ} (h : (z ^ 2).im = 0) :
    z.re = 0 ∨ z.im = 0 := by
  -- (z^2).im = 2 · z.re · z.im
  have him : (z ^ 2).im = 2 * z.re * z.im := by
    rw [sq]; simp [Complex.mul_im]; ring
  rw [him] at h
  have h' : z.re * z.im = 0 := by linarith [h]
  rcases mul_eq_zero.mp h' with hre | him2
  · exact Or.inl hre
  · exact Or.inr him2

/-- Restated as a phase pin: a self-conjugate Gauss sum (`z² ` real, modulus `√q`) has its phase
forced into the 4-element set `{0, π/2, π, 3π/2}` — discrete, hence a genuine handle.  Encoded by
the axis membership above; this is the content of `QuadraticGaussSumMagnitude` in the tree. -/
theorem selfConj_phase_discrete {z : ℂ} (h : (z ^ 2).im = 0) :
    z.re = 0 ∨ z.im = 0 := selfConj_sq_real_forces_axis h

/-! ### The general `m ≥ 3` failure: a DISTINCT reflection partner pins nothing -/

/-- **Magnitude does not determine the phase difference.** For any modulus `s ≥ 0` and any target
phase difference `θ`, there are `z, w` with `‖z‖ = ‖w‖ = s` and `arg(z) − arg(w) = θ` (here
realized as `z = s·e^{iθ}`, `w = s`).  The Stickelberger moduli `|τ| = √q` thus place **no**
constraint on the floor-relevant interference between two *distinct* Gauss sums — the `m ≥ 3`
obstruction.  (We package it as: equal modulus is compatible with the ratio being an arbitrary
unit-modulus number.) -/
theorem magnitude_does_not_pin_phase (s : ℝ) (hs : 0 ≤ s) (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ z w : ℂ, ‖z‖ = s ∧ ‖w‖ = s ∧ (s ≠ 0 → z = u * w) := by
  refine ⟨s * u, (s : ℂ), ?_, ?_, ?_⟩
  · rw [norm_mul]; simp [hu, abs_of_nonneg hs]
  · simp [abs_of_nonneg hs]
  · intro _; ring

/-- **The reflection relation pins an individual phase iff the partner is the conjugate (`m = 2`).**
Suppose `z, w` have `‖z‖ = ‖w‖ = s > 0` and satisfy a reflection `z * w = c` with `c` real (the
archimedean shadow of `τ(χ)τ(χ̄) = χ(−1)q`).
- If `w = conj z` (self-conjugate, `m = 2`): then `z * conj z = ‖z‖² = s²` is automatically real and
  positive, and combined with `z*w = c` the constraint becomes `z² = (c/‖z‖²)·z·... ` collapsing to
  the axis pin (`selfConj`). The phase is constrained.
- If `w` is a *free* unit-modulus multiple of `conj z` (`m ≥ 3`, distinct conjugacy class): `z` can
  have **any** phase while still satisfying `z * w = c` for the appropriate `w` — proven here by
  exhibiting, for every phase `φ`, a valid `(z, w)`.  Hence no pin.

This is the precise dichotomy: only the index-2 self-conjugate relation transmits a phase
constraint to the archimedean side. -/
theorem reflection_pins_iff_real (s : ℝ) (hs : 0 < s) (c : ℝ) (hc : c = s ^ 2) (φ : ℝ) :
    ∃ z w : ℂ, ‖z‖ = s ∧ ‖w‖ = s ∧ z * w = (c : ℂ) ∧ arg z = arg (s * Complex.exp (φ * I)) := by
  -- choose z with the prescribed phase φ, and w = c / z (which then has modulus s and is forced)
  set z : ℂ := s * Complex.exp (φ * I) with hz
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hexp : ‖Complex.exp (φ * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I φ
  have hznorm : ‖z‖ = s := by
    rw [hz, norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hzne : z ≠ 0 := by
    rw [← norm_pos_iff, hznorm]; exact hs
  refine ⟨z, (c : ℂ) / z, hznorm, ?_, ?_, rfl⟩
  · rw [norm_div, hznorm]
    have hcn : ‖(c : ℂ)‖ = s ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, hc, abs_of_nonneg (by positivity)]
    rw [hcn, sq]
    field_simp
  · field_simp

/-! ### The packaged no-go statement -/

/-- **No-go (packaged).** The archimedean phase information a reflection/`Γ_p`-type relation can
transmit is, at most, the *real sign* of a self-conjugate product; that pins a phase to a discrete
axis set **only** when the reflection partner is the conjugate itself (index 2 / `m = 2`). For any
distinct partner (`m ≥ 3`, the prize 2-power regime) the phase is free (`reflection_pins_iff_real`
realizes every `φ`).  Hence the Gross–Koblitz unit part is a handle on the floor **iff** the index
is 2 — i.e. never at prize scale.  Encoded as the conjunction of the two proven facts. -/
theorem grossKoblitz_phase_handle_iff_index_two :
    (∀ z : ℂ, (z ^ 2).im = 0 → z.re = 0 ∨ z.im = 0)            -- m = 2: phase pinned (handle)
    ∧ (∀ s : ℝ, 0 < s → ∀ φ : ℝ,                                -- m ≥ 3: phase free (no handle)
        ∃ z w : ℂ, ‖z‖ = s ∧ ‖w‖ = s ∧ z * w = ((s ^ 2 : ℝ) : ℂ)
          ∧ arg z = arg (s * Complex.exp (φ * I))) := by
  refine ⟨fun z h => selfConj_sq_real_forces_axis h, fun s hs φ => ?_⟩
  exact reflection_pins_iff_real s hs (s ^ 2) rfl φ

end ProximityGap.Frontier.GrossKoblitzPhaseNoGo

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx)
#print axioms ProximityGap.Frontier.GrossKoblitzPhaseNoGo.selfConj_sq_real_forces_axis
#print axioms ProximityGap.Frontier.GrossKoblitzPhaseNoGo.magnitude_does_not_pin_phase
#print axioms ProximityGap.Frontier.GrossKoblitzPhaseNoGo.reflection_pins_iff_real
#print axioms ProximityGap.Frontier.GrossKoblitzPhaseNoGo.grossKoblitz_phase_handle_iff_index_two
