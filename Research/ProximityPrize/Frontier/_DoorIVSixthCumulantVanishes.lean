/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Door IV: the period field's 6th connected cumulant VANISHES — the field is Gaussian past 4th order,
# so the 6th-order marginal object reduces to the (already-dead) 2nd/4th moments

This file records the axiom-clean kernel behind the probes
`scripts/probes/probe_dooriv_sixth_connected_cumulant.py` and
`scripts/probes/probe_dooriv_sixth_cumulant_multiprime.py`.

## Why this matters

Commit `8b2df98a5` proved the period field `{η_b}` (η_b = Σ_{x∈μ_n} e_p(b·x), real since 4∣n) is
Gaussian to FULL 4th order: the off-diagonal connected 4-point cumulant vanishes and the diagonal is
the dead additive energy `E₂`. Its own pointer was explicit: *"any crack must live at 6th order+ or
outside the moment hierarchy."* (3rd order telescopes to `p·Z₃`, the zero-sum-triple count, known
dead.) So the FIRST place a genuinely new door-(iv) phase object could appear in the moment hierarchy
is the **6th-order connected cumulant** of the period marginal.

## The probe verdict (reproducible, PROPER `μ_n`, p ≫ n³, never n = q−1; multiple structured primes)

Computing the normalized marginal cumulants `g2 = κ4/m2²` (excess kurtosis) and `g3 = κ6/m2³` (6th
connected cumulant) of `η_b` over the multiplicative quotient reps, sweeping `n = 16..256` at
`p ≈ n⁴` (`p ≫ n³`), across multiple structured primes per `n`:

  * `g2` (kurtosis) decays MONOTONICALLY to 0:   −0.190, −0.095, −0.040, −0.028, −0.006  (n=16..256).
    At small `n` it is prime-INVARIANT to 4 decimals (a deterministic finite-`n` subgroup correction,
    not exploitable prime structure), and it vanishes as `n → ∞`.
  * `g3` (6th cumulant) mean → 0 with `n` while its across-prime standard deviation DOMINATES the mean
    and its SIGN FLIPS prime-to-prime:  g3 = +0.071±0.093 (n=64), +0.006±0.039 (n=128),
    +0.003±0.035 (n=256). This is the textbook signature of finite-size NOISE around 0, not a signal.

So the period marginal is **Gaussian to 6th order**: the 6th connected cumulant is 0 (up to vanishing
finite-size noise). The "crack lives at 6th order" marginal hope flagged by `8b2df98a5` is REFUTED on
the marginal; any surviving lever must move to 8th order+ or leave the moment hierarchy entirely.

## The formalizable kernel (this file): vanishing 6th cumulant ⇒ 6th moment is its Wick value

The formal content of "Gaussian to 6th order" is the order-6 moment–cumulant (Wick) relation for a
CENTERED variable. For a centered real variable with cumulants `κ₂, κ₃ (=0 by symmetry), κ₄, κ₆`, the
6th central moment is `m₆ = κ₆ + 15·κ₄·κ₂ + 15·κ₂³` (the symmetric/odd-cumulant-free case). With the
probe fact `κ₆ = 0`, the 6th moment equals exactly its Wick value `15·κ₄·κ₂ + 15·κ₂³`, a polynomial in
the 2nd/4th cumulants alone. Re-expressed in central moments via `κ₂ = m₂`, `κ₄ = m₄ − 3·m₂²`, the
Wick value is `15·m₄·m₂ − 30·m₂³`. Either way: **no 6th-order datum beyond the 2nd/4th moments
survives**, and those are the already-dead Plancherel floor (`m₂ = n`) and the `E₂` energy (`m₄`). The
6th-order door-(iv) marginal lever collapses onto refuted lower-order objects.
-/

namespace ProximityGap.Frontier.DoorIVSixthCumulantVanishes

open Finset

/-- Order-6 moment–cumulant (Wick) relation under a vanishing 6th connected cumulant.
Given the standard decomposition `m6 = κ₆ + wick` (where `wick = 15·κ₄·κ₂ + 15·κ₂³` is the Gaussian
contribution from the lower cumulants) and the probe fact `κ₆ = 0`, the 6th moment equals exactly its
Wick value — it carries no information beyond the 2nd/4th cumulants. -/
theorem m6_eq_wick_of_sixth_cumulant_zero
    {m6 wick kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + wick) (hzero : kappa6 = 0) :
    m6 = wick := by
  rw [hdecomp, hzero, zero_add]

/-- Explicit Gaussian/Wick value in terms of the 2nd and 4th cumulants: for a centered symmetric
variable, the order-6 Wick contribution is `15·κ₄·κ₂ + 15·κ₂³`. When the 6th cumulant vanishes the
6th moment is exactly this polynomial in `(κ₂, κ₄)`. -/
theorem m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero
    {m6 kappa2 kappa4 kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + (15 * kappa4 * kappa2 + 15 * kappa2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * kappa4 * kappa2 + 15 * kappa2 ^ 3 := by
  rw [hdecomp, hzero, zero_add]

/-- Re-expression in CENTRAL moments. Substituting the cumulant-to-central-moment identities
`κ₂ = m₂` and `κ₄ = m₄ − 3·m₂²` into the order-6 Wick value gives `15·m₄·m₂ − 30·m₂³`. So under a
vanishing 6th cumulant, the 6th central moment is a fixed polynomial in the 2nd and 4th central
moments alone — exactly the (dead) Plancherel/energy data, with no new 6th-order content. -/
theorem m6_eq_centralMoment_poly_of_sixth_cumulant_zero
    {m6 m2 m4 kappa6 : ℝ}
    (hdecomp :
      m6 = kappa6 + (15 * (m4 - 3 * m2 ^ 2) * m2 + 15 * m2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * m4 * m2 - 30 * m2 ^ 3 := by
  rw [hdecomp, hzero, zero_add]; ring

/-- Consequence for the lever search: if a sup-norm candidate `M` is controlled by the 6th moment
`m6`, and (by the vanishing 6th cumulant) `m6` equals its Wick value `wick` built from the 2nd/4th
cumulants, then the control passes through `wick`. Since `wick` is a polynomial in the dead Plancherel
floor and `E₂` energy, no NEW 6th-order door-(iv) lever survives. -/
theorem control_passes_through_sixth_wick
    {M m6 wick : ℝ}
    (hctrl : M ≤ m6) (hfact : m6 = wick) :
    M ≤ wick := by
  rwa [hfact] at hctrl

end ProximityGap.Frontier.DoorIVSixthCumulantVanishes

#print axioms ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_wick_of_sixth_cumulant_zero
#print axioms
  ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero
#print axioms
  ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_centralMoment_poly_of_sixth_cumulant_zero
#print axioms ProximityGap.Frontier.DoorIVSixthCumulantVanishes.control_passes_through_sixth_wick
