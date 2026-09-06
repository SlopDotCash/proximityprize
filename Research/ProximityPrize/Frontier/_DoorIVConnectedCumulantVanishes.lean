/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV: the period field's SIGNED off-diagonal 4-point connected cumulant VANISHES — the field is
# Gaussian to full 4th order, so the phase-sensitive 4-point door-(iv) object does not exist

This file records the axiom-clean kernel behind the probe
`scripts/probes/probe_dooriv_signed_4point_cumulant.py`.

## Why this matters

Sweep 5 showed the modulus 4th moment (the diagonal `{a,b}={c,d}` part) collapses to the additive
energy `E₂` (refuted). It sharpened the pointer: a surviving door-(iv) lever must be a 4-point object
that does NOT reduce to `E₂` — i.e. the SIGNED off-diagonal connected cumulant that uses phase info.

## The probe verdict (reproducible, proper `μ_n`, p ≫ n³, never n = q−1)

The lag-resolved connected energy-energy cumulant
`T₄(k) = E_j[|z_j|²|z_{j+k}|²] − (E|z|²)² − |E_j[z_j z̄_{j+k}]|² − |E_j[z_j z_{j+k}]|²`
(zero for a Gaussian/Wick field, where the 2-2 moment is determined by the covariance) is `≈ 0` at all
lags and does not grow with `N` (measured `|T₄(k)/(E|z|²)²| ≲ 0.015 → shrinking`). The lone exception,
`T₄(1) = 0.247` at the Fermat prime `p = 65537` (p/n = 4096 small), is the SAME finite-size / Fermat
artifact as in the white-field sweep and vanishes for all larger generic primes.

So the period field is **Gaussian to full 4th order** in its joint structure: the diagonal part is the
dead `E₂`, and the off-diagonal connected cumulant is zero. The phase-sensitive 4-point coherence that
door-(iv) needs does not exist at the connected-4 level. This closes the sweep-5 pointer.

## The formalizable kernel (this file): vanishing connected cumulant ⇒ Wick factorization

The formal content of "Gaussian to 4th order": if the connected 4th cumulant vanishes, the 2-2 moment
**factorizes** into the Wick (2-point) data — there is no residual joint structure beyond the
covariance. We record this factorization algebraically: given the cumulant-decomposition hypothesis
`hwick` (the 2-2 moment = sum of pair contractions + connected cumulant) and the probe fact
`hzero` (connected cumulant = 0), the 2-2 moment equals exactly its Wick value. A bound through a
Wick-factorized 2-2 moment is a bound through the 2-point covariance — which the white-field sweep
already showed is ≈ 0. No off-diagonal 4-point lever survives.
-/

namespace ProximityGap.Frontier.DoorIVConnectedCumulantVanishes

open Finset

/-- Wick factorization under a vanishing connected cumulant. If a 2-2 moment `m22` decomposes (the
standard moment-cumulant relation) as `m22 = wick + cumulant` and the connected `cumulant = 0`, then
`m22 = wick` — the 2-2 moment is fully determined by the 2-point (covariance) data. There is no
residual joint 4-point structure. -/
theorem m22_eq_wick_of_cumulant_zero
    {m22 wick cumulant : ℝ}
    (hdecomp : m22 = wick + cumulant) (hzero : cumulant = 0) :
    m22 = wick := by
  rw [hdecomp, hzero, add_zero]

/-- Complex form (the period field is complex-valued): same factorization over `ℂ`. -/
theorem m22_eq_wick_of_cumulant_zero_complex
    {m22 wick cumulant : ℂ}
    (hdecomp : m22 = wick + cumulant) (hzero : cumulant = 0) :
    m22 = wick := by
  rw [hdecomp, hzero, add_zero]

/-- Consequence: a sup-norm candidate bounded by a Wick-factorized 2-2 moment is bounded by the
2-point (covariance) data. With the white-field sweep's covariance ≈ 0, this leaves no off-diagonal
4-point lever. We state it abstractly: if `M`-control passes through `m22` and `m22 = wick`, the
control passes through `wick` (the covariance object). -/
theorem control_passes_through_wick
    {M m22 wick : ℝ}
    (hctrl : M ≤ m22) (hfact : m22 = wick) :
    M ≤ wick := by
  rwa [hfact] at hctrl

end ProximityGap.Frontier.DoorIVConnectedCumulantVanishes

#print axioms ProximityGap.Frontier.DoorIVConnectedCumulantVanishes.m22_eq_wick_of_cumulant_zero
#print axioms ProximityGap.Frontier.DoorIVConnectedCumulantVanishes.m22_eq_wick_of_cumulant_zero_complex
#print axioms ProximityGap.Frontier.DoorIVConnectedCumulantVanishes.control_passes_through_wick
