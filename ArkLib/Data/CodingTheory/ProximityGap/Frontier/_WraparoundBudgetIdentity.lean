/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The wraparound-budget identity — the prize reduces to ONE inequality on `W_r` (#444)

This file lands the **exact algebraic reduction** of the Ethereum proximity prize (#444) at a fixed
depth `r` to a single inequality on the genuine mod-`p` *wraparound count* `W_r` (the char-`p`
excess of the `2r`-th BGK moment over its char-`0` value), carrying the two non-negative credits
that the prize budget is allowed to spend.

## The setup (defs, recalled — proven elsewhere in-tree)

For `μ_n = ` the `2^μ`-th roots of unity in `F_p` (`n = 2^μ`), `η_b = Σ_{x∈μ_n} e_p(b·x)`, the prize
is `M(μ_n) = max_{b≠0} |η_b| ≤ C·√(n·log m)`, equivalent (via the moment method at the saddle
`r ≈ log p`) to the **DC-subtracted moment bound**

  `S_r := Σ_{b≠0} |η_b|^{2r} ≤ (p−1)·Wick_r`,   `Wick_r = (2r−1)‼·n^r`.

In-tree DC-correct objects give the algebraic skeleton:

* `DCSubtractedMoment.sum_nonzero_moment` : `S_r = p·E_r(F_p) − n^{2r}` (DC term removed),
* `E_r(F_p) = E_r(ℂ) + W_r` with `W_r ≥ 0` the genuine mod-`p` wraparound count,
* `Δ_r = Wick_r − E_r(ℂ) ≥ 0` the **char-0 deficit** (Lam–Leung / Bessel; char-0 side closed).

## The identity (this file, abstract over ℝ)

Writing `S = S_r`, `E0 = E_r(ℂ)`, `W = W_r`, `Wick = Wick_r`, `Delta = Δ_r`, `p`, `n`, `r` as real
parameters tied only by the two **defining relations**

  `hS    : S     = p·(E0 + W) − n^(2r)`     (`S_r = p·E_r(F_p) − n^{2r}`, `E_r(F_p) = E0 + W`)
  `hDelta: Delta = Wick − E0`               (char-0 deficit),

the prize inequality at depth `r` is **equivalent** to a single budget inequality on `W`:

  `S ≤ (p−1)·Wick   ↔   p·W ≤ n^(2r) − Wick + p·Delta`.

The right-hand side exposes the two non-negative credits the prize may spend against the wraparound
mass `p·W`: the **DC headroom** `n^(2r) − Wick` and the **char-0 deficit credit** `p·Delta`. The
whole prize, at each depth `r`, is exactly this one inequality on the wraparound count `W_r`.

## Status

This is **pure ring rearrangement** — `(p−1)·Wick = p·Wick − Wick`, then move equal quantities
across the inequality (no sign hypotheses are needed; the equivalence is unconditional in the
parameters). It is the honest *launchpad* brick: it does not bound `W_r` (that is the open wall, the
incidence / `√q·B` cancellation), it only certifies that the prize collapses to that one bound.
Fully proven, axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

namespace ArkLib.ProximityGap.Frontier.WraparoundBudgetIdentity

/-- **The wraparound-budget identity (#444).** Over the reals, given the two defining relations
`S = p·(E0 + W) − n^(2r)` (the DC-subtracted moment, with `E_r(F_p) = E0 + W`) and
`Delta = Wick − E0` (the char-0 deficit), the prize inequality `S ≤ (p−1)·Wick` is **equivalent**
to the single wraparound-budget inequality `p·W ≤ n^(2r) − Wick + p·Delta`.

This is pure ring rearrangement: it carries no sign hypotheses and bounds nothing — it certifies
that the prize at depth `r` reduces to exactly one inequality on the wraparound count `W`, with the
two non-negative credits (DC headroom `n^(2r) − Wick`, char-0 deficit credit `p·Delta`) made
explicit on the right. -/
theorem prize_iff_wraparound_budget
    (S Wick E0 W Delta p n r : ℝ)
    (hS : S = p * (E0 + W) - n ^ (2 * r))
    (hDelta : Delta = Wick - E0) :
    S ≤ (p - 1) * Wick ↔ p * W ≤ n ^ (2 * r) - Wick + p * Delta := by
  subst hS hDelta
  constructor
  · intro h; nlinarith [h]
  · intro h; nlinarith [h]

/-- **Equational core**, isolating the algebra: the "prize slack" `(p−1)·Wick − S` equals the
"budget slack" `(n^(2r) − Wick + p·Delta) − p·W`. Both `↔` directions of
`prize_iff_wraparound_budget` are immediate from this single identity (a difference of two sides
is preserved, so each inequality `… ≥ 0` is the same statement). -/
theorem prize_slack_eq_budget_slack
    (S Wick E0 W Delta p n r : ℝ)
    (hS : S = p * (E0 + W) - n ^ (2 * r))
    (hDelta : Delta = Wick - E0) :
    (p - 1) * Wick - S = (n ^ (2 * r) - Wick + p * Delta) - p * W := by
  subst hS hDelta; ring

end ArkLib.ProximityGap.Frontier.WraparoundBudgetIdentity
