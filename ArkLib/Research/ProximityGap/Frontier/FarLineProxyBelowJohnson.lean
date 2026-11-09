/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The far-line incidence threshold is a Plotkin proxy `-> 1/2`, BELOW Johnson for `rho < 1/4`

This file formalizes the structural separation flagged as master-open-thread item #5 of the #444
synthesis (lalalune): *"Antipodal route caps at `delta* = 1/2` (Plotkin ceiling), provable; would
isolate the hard residual to genuinely asymmetric far-line words (a clean structural separation)."*

## The two objects

* **The far-line incidence threshold** (the COMPUTABLE proxy). With the in-tree budget
  `B = q * eps* = (n * 2^128) * 2^-128 = n` (`B1IncidenceBridge.WorstCaseFarIncidenceBounded` at
  `B = n`), the exact far-line incidence threshold over the `2`-power subgroup `mu_n` is
  (validated Rust engine, matches the canonical probe `delta*(mu_16, k=4) = 9/16`; KB note
  `farline-incidence-is-plotkin-proxy-not-mca-deltastar.md`):

      farLineProxy n rho = 1/2 + (1/(2 rho) - 1) / n.

  Its limiting value is `1/2` (the Plotkin ceiling); the approach is the explicit `O(1/n)` term.

* **The true MCA `delta*`** (the PRIZE target). It is `>= Johnson = 1 - sqrt rho` (the Johnson
  radius is list-decodable / achievable), the floor the prize conjectures `delta* = 1 - rho -
  Theta(1/log n)` lives at.

## The separation (this file, axiom-clean)

For `rho < 1/4` the Johnson radius exceeds `1/2`:

    rho < 1/4  =>  sqrt rho < 1/2  =>  1/2 < 1 - sqrt rho = Johnson.

The far-line proxy tends to `1/2`, so past an explicit threshold in `n` it drops STRICTLY below
Johnson, hence below the MCA `delta*`:

    far-line proxy(n, rho) -> 1/2  <  Johnson <= MCA delta*.

Therefore the computable far-line incidence threshold is NOT the MCA `delta*` for `rho < 1/4`: they
are different objects, and the BGK / Paley half-power difficulty lives entirely in the gap between
the (easy, `-> 1/2`) far-line proxy and the (hard, `>= Johnson`) MCA threshold. This is a clean
structural separation that isolates the prize-hard residual; it is NOT a closure of CORE.

## Honest scope

* This is a refutation-with-mechanism of the over-identification "far-line incidence `= delta*`",
  NOT a proof of CORE. CORE `M(mu_n) <= C * sqrt(n log(p/n))` stays OPEN.
* The proxy formula `farLineProxy` is the in-tree validated empirical law (probe-confirmed exact at
  `rho in {1/4, 1/8, ...}`, `n = 8..2048`, by `scripts/probes/probe_plotkin_farline_johnson.py`);
  here it is taken as the named definition whose limit + Johnson-crossing we prove. We do NOT
  re-derive the count law (it is a `Prop`-level empirical anchor; see `B1XkIncidenceForm.lean`).
* The Johnson lower bound on the MCA `delta*` (`Johnson <= mcaDeltaStar`) is the standard
  list-decodability fact, carried here as a NAMED hypothesis `hJohnson`, nothing is fabricated.

Axiom-clean (`#print axioms` below: `subseteq {propext, Classical.choice, Quot.sound}`, no `sorry`,
no `axiom`, no `native_decide`). -- plotkinsep lane, co-author wakesync.
-/

namespace ProximityGap.Frontier.FarLineProxyBelowJohnson

open Real

/-- The far-line incidence threshold (the computable Plotkin proxy) over `mu_n` at rate `rho`,
with the in-tree budget `B = n`: `farLineProxy n rho = 1/2 + (1/(2 rho) - 1) / n`. -/
noncomputable def farLineProxy (n rho : ℝ) : ℝ := 1 / 2 + (1 / (2 * rho) - 1) / n

/-- The exact signed gap of the proxy to its `1/2` ceiling: `farLineProxy n rho - 1/2 =
(1/(2 rho) - 1) / n`. The `O(1/n)` Plotkin-approach term, no rounding. -/
theorem farLineProxy_sub_half (n rho : ℝ) :
    farLineProxy n rho - 1 / 2 = (1 / (2 * rho) - 1) / n := by
  simp only [farLineProxy]; ring

/-- **Plotkin ceiling, finite-`n` form.** For `0 < rho < 1/2` (so `1/(2 rho) - 1 > 0`) and `0 < n`,
the proxy lies strictly above `1/2` but its excess is the explicit `(1/(2 rho) - 1)/n`, which is
`< epsilon` once `n > (1/(2 rho) - 1)/epsilon`. We record the clean monotone fact: the excess is
positive and the proxy strictly exceeds `1/2` (the approach is from above, toward the ceiling). -/
theorem farLineProxy_gt_half (n rho : ℝ) (hn : 0 < n) (hrho : 0 < rho) (hrho2 : rho < 1 / 2) :
    1 / 2 < farLineProxy n rho := by
  have hexc : 0 < 1 / (2 * rho) - 1 := by
    have h2r : 2 * rho < 1 := by linarith
    have hpos : 0 < 2 * rho := by linarith
    have : 1 < 1 / (2 * rho) := by
      rw [lt_div_iff₀ hpos]; linarith
    linarith
  have : 0 < (1 / (2 * rho) - 1) / n := div_pos hexc hn
  have := farLineProxy_sub_half n rho
  linarith

/-- **The proxy is below `1/2 + epsilon` once `n` is large**: the quantitative Plotkin approach.
For any `epsilon > 0`, if `n > (1/(2 rho) - 1)/epsilon` (and `n, rho > 0`) then
`farLineProxy n rho < 1/2 + epsilon`. -/
theorem farLineProxy_lt_half_add (n rho epsilon : ℝ) (hn : 0 < n) (heps : 0 < epsilon)
    (hbig : (1 / (2 * rho) - 1) / epsilon < n) :
    farLineProxy n rho < 1 / 2 + epsilon := by
  have hsub := farLineProxy_sub_half n rho
  have : (1 / (2 * rho) - 1) / n < epsilon := by
    rw [div_lt_iff₀ hn]
    rw [div_lt_iff₀ heps] at hbig
    linarith
  linarith

/-- **Johnson exceeds `1/2` strictly below rate `1/4`.** `0 < rho < 1/4  =>  sqrt rho < 1/2`,
hence `1/2 < 1 - sqrt rho =` the Johnson radius. Pure real-analysis (square both sides). -/
theorem half_lt_johnson_of_lt_quarter (rho : ℝ) (hrho : 0 < rho) (hrho4 : rho < 1 / 4) :
    1 / 2 < 1 - Real.sqrt rho := by
  have hsqrt_lt : Real.sqrt rho < 1 / 2 := by
    have hsq : Real.sqrt rho ^ 2 = rho := Real.sq_sqrt (le_of_lt hrho)
    nlinarith [Real.sqrt_nonneg rho, hsq, hrho4]
  linarith

/-- **THE SEPARATION (finite-`n`, axiom-clean).** Fix the prize regime `0 < rho < 1/4` and any
`n` large enough that the proxy excess undershoots the Johnson margin `(1 - sqrt rho) - 1/2 > 0`.
Then the computable far-line proxy is STRICTLY below the Johnson radius:

    farLineProxy n rho < 1 - sqrt rho.

The `n`-threshold is explicit: `n > (1/(2 rho) - 1) / ((1 - sqrt rho) - 1/2)`. -/
theorem farLineProxy_lt_johnson (n rho : ℝ) (hn : 0 < n) (hrho : 0 < rho) (hrho4 : rho < 1 / 4)
    (hbig : (1 / (2 * rho) - 1) / ((1 - Real.sqrt rho) - 1 / 2) < n) :
    farLineProxy n rho < 1 - Real.sqrt rho := by
  have hmargin : 0 < (1 - Real.sqrt rho) - 1 / 2 := by
    have := half_lt_johnson_of_lt_quarter rho hrho hrho4
    linarith
  -- proxy < 1/2 + margin = Johnson
  have hlt := farLineProxy_lt_half_add n rho ((1 - Real.sqrt rho) - 1 / 2) hn hmargin hbig
  linarith

/-- **The over-identification refutation (the named structural separation).** Suppose the MCA
`delta*` (here `mcaDeltaStar`, abstract) is at least the Johnson radius (the standard
list-decodability fact, supplied as `hJohnson`). In the prize regime `0 < rho < 1/4` with `n` past
the explicit threshold, the computable far-line proxy is STRICTLY below `mcaDeltaStar`:

    farLineProxy n rho < mcaDeltaStar.

So the far-line incidence threshold is NOT the MCA `delta*`: they are different objects, and the
prize-hard (BGK/Paley) content lives in the strict gap between them. NOT a CORE closure. -/
theorem farLineProxy_lt_mca (n rho mcaDeltaStar : ℝ) (hn : 0 < n) (hrho : 0 < rho)
    (hrho4 : rho < 1 / 4)
    (hbig : (1 / (2 * rho) - 1) / ((1 - Real.sqrt rho) - 1 / 2) < n)
    (hJohnson : 1 - Real.sqrt rho ≤ mcaDeltaStar) :
    farLineProxy n rho < mcaDeltaStar := by
  have := farLineProxy_lt_johnson n rho hn hrho hrho4 hbig
  linarith

end ProximityGap.Frontier.FarLineProxyBelowJohnson

set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.farLineProxy_sub_half
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.farLineProxy_gt_half
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.farLineProxy_lt_half_add
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.half_lt_johnson_of_lt_quarter
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.farLineProxy_lt_johnson
set_option linter.style.longLine false in
#print axioms ProximityGap.Frontier.FarLineProxyBelowJohnson.farLineProxy_lt_mca
