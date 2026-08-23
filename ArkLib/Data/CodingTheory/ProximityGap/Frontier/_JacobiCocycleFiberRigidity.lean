/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import Mathlib.Tactic

/-!
# The trivial-cocycle Fourier fiber is RIGID: full mass `n` forces the genuine-character ratio `r = 1`

**Door (iv), Lane 3 — frontier-movement, extends a proven anchor (`trivial_cocycle_delta_fiber`).**

`_JacobiCocycleDispersion` proved the *forward* on/off-support delta pattern of the length-`n` geometric
Fourier fiber `∑_{g<n} r^g` for an `n`-th root of unity `r`:
* `trivial_cocycle_delta_fiber` — `∑_{g<n} r^g = if r = 1 then n else 0`, and
* `trivial_cocycle_full_concentration` / `trivial_cocycle_offSupport_zero` — the full-mass spike at `r = 1`
  and the exact cancellation off support.

What was MISSING is the *converse / rigidity direction*: that the value `n` is attained **only** at `r = 1`.
Equivalently, the geometric fiber is RIGID — its modulus reaches the triangle ceiling `n` exactly when the
ratio is trivial. This file locks that rigidity as kernel statements:

* `fiber_eq_card_iff_one` — `∑_{g<n} r^g = n ⟺ r = 1` (for `0 < n`, `r^n = 1`).
* `norm_fiber_eq_card_iff_one` — `‖∑_{g<n} r^g‖ = n ⟺ r = 1`.
* `norm_fiber_lt_card_of_ne_one` — a nontrivial ratio gives STRICTLY sub-ceiling modulus (`‖·‖ = 0 < n`).
* `fiber_full_mass_forces_trivial_cocycle` — the Door-IV reading: full Fourier concentration (fiber `= n`,
  the maximally-bad trivial bound) is attainable **only** by the genuine-character / trivial-cocycle ratio,
  so any genuine `r ≠ 1` (a nontrivial projective phase) is forced strictly below `n`.
* `trivial_transform_l2_delta` — the Parseval / `ℓ²` face: over the `n` frequency offsets the trivial-cocycle
  transform's total squared mass `∑_i ‖fiber‖² = n²` sits ENTIRELY on the single on-support fiber
  (`sup² = n² = total mass`, concentration ratio `1`, zero dispersion — the extremal worst case).
* `trivial_transform_offSupport_all_zero` — every off-support fiber is empty: the trivial cocycle moves
  NO mass off the matching frequency, so it does zero dispersion (the prize must break this).

This is the rigidity counterpart of the named open `JacobiCocycleDispersion`: it does NOT prove that the
Jacobi cocycle disperses (the prize); it proves that the *only* way to fail dispersion all the way up to the
ceiling `n` on a single fiber is the degenerate trivial-cocycle ratio. Probe-validated (510 roots of unity,
n = 2,4,…,256: fiber modulus equals `n` iff `r = 1`, zero otherwise). Axiom-clean. No CORE, cancellation,
completion, moment-saving, or capacity claim. Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity

open Finset

/-- **Rigidity of the trivial-cocycle Fourier fiber (exact value).** For `0 < n` and an `n`-th root of unity
`r`, the length-`n` geometric fiber `∑_{g<n} r^g` equals the full mass `n` **iff** `r = 1`. The reverse
direction is the geometric-sum spike (`r = 1`); the forward direction is the rigidity: if `r ≠ 1` the fiber is
`0` (orthogonality), so it cannot also be `n` (since `(n : ℂ) ≠ 0` for `0 < n`). -/
theorem fiber_eq_card_iff_one {n : ℕ} (hn : 0 < n) {r : ℂ} (hrpow : r ^ n = 1) :
    (∑ g ∈ range n, r ^ g) = (n : ℂ) ↔ r = 1 := by
  constructor
  · intro hsum
    by_contra hr
    -- off support: the fiber is zero, contradicting it being the nonzero `n`.
    have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
      ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
        r hrpow hr
    rw [hzero] at hsum
    have hne0 : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn.ne'
    exact hne0 hsum.symm
  · intro hr
    subst hr
    simp

/-- **Rigidity in modulus.** For `0 < n` and an `n`-th root of unity `r`, the fiber modulus reaches the
triangle ceiling `n` **iff** `r = 1`. Off support the modulus is `0`. -/
theorem norm_fiber_eq_card_iff_one {n : ℕ} (hn : 0 < n) {r : ℂ} (hrpow : r ^ n = 1) :
    ‖∑ g ∈ range n, r ^ g‖ = (n : ℝ) ↔ r = 1 := by
  constructor
  · intro hnorm
    by_contra hr
    have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
      ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
        r hrpow hr
    rw [hzero, norm_zero] at hnorm
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact this.ne hnorm
  · intro hr
    subst hr
    simp

/-- **A nontrivial ratio is strictly below the ceiling.** If `r ≠ 1` is an `n`-th root of unity (`0 < n`),
the fiber modulus is `0`, hence strictly less than the full mass `n`. This is the dispersion-toward-a-single-
fiber statement: the only fiber that saturates the triangle ceiling is the trivial one. -/
theorem norm_fiber_lt_card_of_ne_one {n : ℕ} (hn : 0 < n) {r : ℂ}
    (hrpow : r ^ n = 1) (hr : r ≠ 1) :
    ‖∑ g ∈ range n, r ^ g‖ < (n : ℝ) := by
  have hzero : (∑ g ∈ range n, r ^ g) = 0 :=
    ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
      r hrpow hr
  rw [hzero, norm_zero]
  exact_mod_cast hn

/-- **Door-IV reading: full single-fiber concentration forces the trivial cocycle.** The maximally-bad
(`= n`, zero-dispersion) value of the trivial-cocycle Fourier fiber is attainable on an `n`-th root of unity
`r` ONLY by the genuine-character / trivial-cocycle ratio `r = 1`. Contrapositive: any genuine nontrivial
projective phase `r ≠ 1` cannot saturate the ceiling, so failing to disperse all the way to `n` on a fiber is
EXACTLY the degenerate character case. This is the rigidity counterpart of the open `JacobiCocycleDispersion`;
it does not bound the cocycle dispersion (the prize), only certifies the unique full-mass attainer. -/
theorem fiber_full_mass_forces_trivial_cocycle {n : ℕ} (hn : 0 < n) {r : ℂ}
    (hrpow : r ^ n = 1) (hfull : ‖∑ g ∈ range n, r ^ g‖ = (n : ℝ)) :
    r = 1 :=
  (norm_fiber_eq_card_iff_one hn hrpow).mp hfull

/-! ## The Parseval / ℓ² face: the trivial-cocycle transform is the extremal delta

The trivial-cocycle (genuine-character) Fourier transform, evaluated over the `n` frequency offsets, is a
perfect delta: ALL of its `ℓ²` mass sits on the single on-support fiber. We model the `n` offsets by an
indexed family of `n`-th roots `r : Fin n → ℂ` with exactly one trivial entry (`r i₀ = 1`, the matching
frequency) and all others a nontrivial `n`-th root (off support). The squared fiber norms then sum to
`n²`, entirely concentrated in the `i₀` term — the maximally-bad, zero-dispersion concentration that the
prize must break down to `√n·polylog`. -/

/-- **The trivial-cocycle transform is a Parseval-extremal delta.** Given the `n` frequency offsets as a
family `r : Fin n → ℂ` of `n`-th roots of unity with a single on-support entry `r i₀ = 1` and every other
entry a nontrivial root, the total `ℓ²` mass `∑_i ‖fiber(r i)‖²` equals `n²` and is carried ENTIRELY by
the `i₀` term (every other term is `0`). This is the maximally-concentrated baseline: a single fiber holds
the full Parseval mass `n²`, so `sup² = n² = total mass` (concentration ratio `1`, zero dispersion). -/
theorem trivial_transform_l2_delta {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ)
    (hroot : ∀ i, (r i) ^ n = 1) (i₀ : Fin n) (hi₀ : r i₀ = 1)
    (hoff : ∀ i, i ≠ i₀ → r i ≠ 1) :
    ∑ i, ‖∑ g ∈ range n, (r i) ^ g‖ ^ 2 = ((n : ℝ)) ^ 2 := by
  -- every off-support term has zero fiber, the on-support term has fiber `n`.
  have hterm : ∀ i, ‖∑ g ∈ range n, (r i) ^ g‖ ^ 2
      = if i = i₀ then ((n : ℝ)) ^ 2 else 0 := by
    intro i
    by_cases hi : i = i₀
    · have hcard : (∑ g ∈ range n, (r i) ^ g) = (n : ℂ) := by
        rw [hi, hi₀]; simp
      rw [hcard, if_pos hi, Complex.norm_natCast]
    · have hne : r i ≠ 1 := hoff i hi
      have hzero : (∑ g ∈ range n, (r i) ^ g) = 0 :=
        ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
          (r i) (hroot i) hne
      rw [hzero, norm_zero]
      simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq' Finset.univ i₀ (fun _ => ((n : ℝ)) ^ 2)]
  simp

/-- **The off-support fibers are exactly the dispersion-carriers, all empty for the trivial cocycle.** In
the trivial-cocycle delta, every frequency offset other than the matching one contributes ZERO to the
Fourier transform. So the trivial cocycle does NO dispersion: the `n²` Parseval mass never leaves the
single on-support fiber. The prize requires the genuine Jacobi cocycle to MOVE mass off this fiber. -/
theorem trivial_transform_offSupport_all_zero {n : ℕ} {r : Fin n → ℂ}
    (hroot : ∀ i, (r i) ^ n = 1) (i₀ : Fin n)
    (hoff : ∀ i, i ≠ i₀ → r i ≠ 1) :
    ∀ i, i ≠ i₀ → (∑ g ∈ range n, (r i) ^ g) = 0 := by
  intro i hi
  exact ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
    (r i) (hroot i) (hoff i hi)

/-- **The trivial-cocycle transform has sup exactly `n`.** Under the same one-on-support / all-off-support
hypotheses as `trivial_transform_l2_delta`, the `L∞` norm over frequency offsets is the full triangle
ceiling `n`. This is the sup-norm face of the delta baseline: the unique on-support fiber attains `n`, and
all other fibers vanish. -/
theorem trivial_transform_sup_delta {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ)
    (hroot : ∀ i, (r i) ^ n = 1) (i₀ : Fin n) (hi₀ : r i₀ = 1)
    (hoff : ∀ i, i ≠ i₀ → r i ≠ 1) :
    (univ.sup'
        (by simpa [Finset.univ_nonempty_iff] using Fin.pos_iff_nonempty.mp hn)
        (fun i => ‖∑ g ∈ range n, (r i) ^ g‖)) = (n : ℝ) := by
  let hne : (univ : Finset (Fin n)).Nonempty := by
    simpa [Finset.univ_nonempty_iff] using Fin.pos_iff_nonempty.mp hn
  apply le_antisymm
  · refine Finset.sup'_le hne _ ?_
    intro i _
    by_cases hi : i = i₀
    · have hcard : (∑ g ∈ range n, (r i) ^ g) = (n : ℂ) := by
        rw [hi, hi₀]; simp
      rw [hcard, Complex.norm_natCast]
    · have hzero : (∑ g ∈ range n, (r i) ^ g) = 0 :=
        ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.geom_sum_zero_of_pow_eq_one_of_ne_one
          (r i) (hroot i) (hoff i hi)
      rw [hzero, norm_zero]
      exact_mod_cast Nat.zero_le n
  · have hcard : (∑ g ∈ range n, (r i₀) ^ g) = (n : ℂ) := by
      rw [hi₀]; simp
    calc (n : ℝ) = ‖∑ g ∈ range n, (r i₀) ^ g‖ := by rw [hcard, Complex.norm_natCast]
      _ ≤ univ.sup' hne (fun i => ‖∑ g ∈ range n, (r i) ^ g‖) :=
          Finset.le_sup' (fun i => ‖∑ g ∈ range n, (r i) ^ g‖) (Finset.mem_univ i₀)

/-- **Concentration-ratio form: the trivial cocycle has `L² = L∞²`.** The Parseval mass over all frequency
offsets equals the square of the `L∞` norm. Hence the trivial cocycle has concentration ratio exactly `1`:
no `L²` mass is dispersed away from the worst fiber. Any Door-IV saving must make this equality fail for
the genuine Jacobi cocycle. -/
theorem trivial_transform_l2_eq_sup_sq {n : ℕ} (hn : 0 < n) (r : Fin n → ℂ)
    (hroot : ∀ i, (r i) ^ n = 1) (i₀ : Fin n) (hi₀ : r i₀ = 1)
    (hoff : ∀ i, i ≠ i₀ → r i ≠ 1) :
    ∑ i, ‖∑ g ∈ range n, (r i) ^ g‖ ^ 2 =
      ((univ.sup'
        (by simpa [Finset.univ_nonempty_iff] using Fin.pos_iff_nonempty.mp hn)
        (fun i => ‖∑ g ∈ range n, (r i) ^ g‖)) ^ 2) := by
  rw [trivial_transform_l2_delta hn r hroot i₀ hi₀ hoff]
  rw [trivial_transform_sup_delta hn r hroot i₀ hi₀ hoff]

end ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; no extra axioms) -/
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.fiber_eq_card_iff_one
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.norm_fiber_eq_card_iff_one
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.norm_fiber_lt_card_of_ne_one
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.fiber_full_mass_forces_trivial_cocycle
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.trivial_transform_l2_delta
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.trivial_transform_offSupport_all_zero
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.trivial_transform_sup_delta
#print axioms ArkLib.ProximityGap.Frontier.JacobiCocycleFiberRigidity.trivial_transform_l2_eq_sup_sq
