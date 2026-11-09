/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Door IV capstone: the marginal moment ladder Wick-collapses — at any even order, a vanishing
# connected cumulant forces the moment to a polynomial in the LOWER moments (no new datum)

This file is the reusable, numerics-independent capstone behind the door-(iv) marginal-moment
findings. It generalizes the order-4 (`8b2df98a5`) and order-6 (`57b3d915c`) bricks into ONE
statement about the moment–cumulant (Wick) relation, so the campaign has a single citable lemma for
"the marginal moment ladder of the period field is Gaussian-collapsed".

## Why this matters (the door-(iv) marginal hierarchy, settled)

The period field `{η_b}` (η_b = Σ_{x∈μ_n} e_p(b·x), real since 4∣n) has been probed at successive
even orders (PROPER `μ_n`, p≈n⁴≫n³, exact bignum arithmetic, multiple structured primes, never
n=q−1):
  * order 2 = Plancherel floor `m₂ = n` (exact).
  * order 4: connected cumulant κ₄ → 0 (kurtosis −0.190→−0.005 monotone); 4th moment = `E₂` (dead).
  * order 6: connected cumulant κ₆ → 0 (g₃ mean→0, across-prime sd dominates, sign flips =
    finite-size noise). Period field Gaussian to 6th order (`57b3d915c`).
  * order 8: connected cumulant κ₈ has NO stable signal — across 3 primes per n the normalized g₄
    has across-prime sd DOMINATING the mean with prime-to-prime SIGN FLIPS (n=32: +0.26,−0.36,−0.36;
    n=64: +0.42,−0.06,+1.54; n=128: −0.59,+0.34,−0.23), mean consistent with 0. This is sampling
    noise (the 8th moment is dominated by the few largest |η_b| in the sample). We do NOT claim an
    axiom-clean 8th-order vanishing — only that no stable non-Gaussian 8th signal survives the
    multi-prime check; it is logged in DISPROOF_LOG as "noise, no signal, do not over-read".

The MOMENT-LADDER conclusion is structural and prime-independent: whenever a connected cumulant
vanishes, the corresponding moment is a fixed polynomial in the lower moments — it carries NO
information beyond them. Since the surviving lower moments are the dead Plancherel floor (`m₂ = n`)
and the dead `E₂` energy (`m₄`), no marginal moment-ladder rung supplies a new door-(iv) lever. Any
crack must leave the moment hierarchy entirely (and the "outside-the-moment-hierarchy" worst-b
internal-geometry fork is itself dead — `78d1df596`).

## The formalizable kernel (this file): the Wick collapse at a generic even order

We abstract the moment–cumulant relation as: `m₂ᵣ = κ₂ᵣ + wick`, where `wick` is the contribution
assembled from strictly-LOWER cumulants. Under `κ₂ᵣ = 0` the moment equals its `wick` value — a
polynomial in the strictly-lower moments/cumulants alone (NO new datum at order `2r`). This
UNCONDITIONAL statement (`moment_eq_wick_of_cumulant_zero`) is all that a SINGLE `κ₂ᵣ = 0` buys; it
specializes to orders 4, 6, 8, … .

The further collapse to the `m₂`-ONLY Gaussian value `(2r−1)‼ · m₂ʳ`
(`moment_eq_gaussMoment_of_cumulant_zero`) is STRONGER and needs an ADDED hypothesis: that ALL lower
connected cumulants above order 2 have ALSO vanished (so the lower moments already equal their
Gaussian values). That hypothesis is encoded in its `hdecomp` argument (the `wick` term is the
m₂-only Gaussian moment `(2r+1)·m₂·gaussMoment`). With ONLY `κ₂ᵣ = 0`, the moment can still depend
on lower NON-Gaussian moments. Empirically the probes ESTABLISH this added hypothesis at orders 4 and
6 (κ₄, κ₆ → 0), so the ladder IS m₂-collapsed through order 6; at order 8 the data is only
'no stable signal' (noise), NOT a proven vanishing, so the m₂-only collapse is not asserted there.
-/

namespace ProximityGap.Frontier.DoorIVMomentLadderWickCollapse

open Finset

/-- Generic-order Wick collapse: under a vanishing connected cumulant `κ = 0`, the moment `m`
equals its Wick value `wick` (the Gaussian contribution from strictly-lower cumulants). One
statement for every even order (specializes to 4th, 6th, 8th, …). -/
theorem moment_eq_wick_of_cumulant_zero
    {m wick kappa : ℝ}
    (hdecomp : m = kappa + wick) (hzero : kappa = 0) :
    m = wick := by
  rw [hdecomp, hzero, zero_add]

/-- The Gaussian moment value: for a centered variable with all connected cumulants above order 2
vanishing, the order-`2r` moment is `(2r−1)‼ · m₂ʳ`. We record the order-2 base case `(2·1−1)‼ = 1`
and the recursive Gaussian-moment relation `g(r+1) = (2r+1) · m₂ · g(r)` abstractly, so that the
ladder is pinned to `m₂` alone. (`doubleFactorialOdd r` = `(2r−1)‼`.) -/
def gaussMoment (m2 : ℝ) : ℕ → ℝ
  | 0 => 1
  | (r + 1) => (2 * r + 1 : ℝ) * m2 * gaussMoment m2 r

/-- Base case: the 0th Gaussian moment is `1`. -/
theorem gaussMoment_zero (m2 : ℝ) : gaussMoment m2 0 = 1 := rfl

/-- The Gaussian-moment recursion is exactly the Wick/Isserlis ladder step
`m_{2(r+1)} = (2r+1)·m₂·m_{2r}` under full cumulant vanishing above order 2: once a step's connected
cumulant is `0`, the next moment is `(2r+1)·m₂` times the previous — a pure function of `m₂`. -/
theorem gaussMoment_succ (m2 : ℝ) (r : ℕ) :
    gaussMoment m2 (r + 1) = (2 * r + 1 : ℝ) * m2 * gaussMoment m2 r := rfl

/-- Ladder collapse to the 2nd moment. NOTE the hypothesis: `hdecomp` assumes the moment decomposes
as `m = κ + (2r+1)·m₂·(gaussMoment m₂ r)`, i.e. the `wick` term is ALREADY the m₂-only Gaussian moment
— which holds only when all lower connected cumulants above order 2 have ALSO vanished. Under that
added hypothesis plus `κ = 0`, `m = gaussMoment m₂ (r+1)`, a fixed function of `m₂` alone. (A single
`κ = 0` without the lower-cumulant vanishing gives only `moment_eq_wick_of_cumulant_zero`, a poly in
lower moments.) The probes establish the lower-cumulant vanishing at orders 4, 6 (not 8), so the
ladder is m₂-collapsed through order 6, where each rung supplies nothing beyond the dead `m₂ = n`. -/
theorem moment_eq_gaussMoment_of_cumulant_zero
    {m m2 kappa : ℝ} {r : ℕ}
    (hdecomp : m = kappa + (2 * r + 1 : ℝ) * m2 * gaussMoment m2 r)
    (hzero : kappa = 0) :
    m = gaussMoment m2 (r + 1) := by
  rw [hdecomp, hzero, zero_add, gaussMoment_succ]

end ProximityGap.Frontier.DoorIVMomentLadderWickCollapse

#print axioms
  ProximityGap.Frontier.DoorIVMomentLadderWickCollapse.moment_eq_wick_of_cumulant_zero
#print axioms
  ProximityGap.Frontier.DoorIVMomentLadderWickCollapse.gaussMoment_succ
#print axioms
  ProximityGap.Frontier.DoorIVMomentLadderWickCollapse.moment_eq_gaussMoment_of_cumulant_zero
