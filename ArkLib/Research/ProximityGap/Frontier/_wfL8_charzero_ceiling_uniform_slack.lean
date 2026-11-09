/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L8, #444)
-/
import ArkLib.Research.ProximityGap.Frontier._CharZeroWickEnergy

/-!
# The char-`0` Lam–Leung ceiling, UNIFORM in `r`, on the real `rEnergy` carrier (#444, wf-L8)

## What this file proves

`CharZeroWickEnergy.gaussianEnergyBound_dyadic` (#407) proves, with NO per-`r` hypothesis,

> `GaussianEnergyBound G r`  i.e.  `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r`

for any finset `G ⊆ μ_{2^k}` (`k ≥ 1`, char-`0`, negation-closed — automatic for `μ_{2^k}`).  This file
re-exports it as `charzero_ceiling_uniform` and records the trivial `Spur = 0` faithfulness-edge corollary.

## Correction (audit 2026-10-28, CW-B18-08): the ceiling is NOT a load-bearing slack-route input

An earlier version of this file claimed to "discharge" the slack route's free hypothesis
`hZceiling : Z ≤ ceiling` uniformly in `r`, and to "wire" that discharge into `slack_route_full`.
That framing was wrong.  The slack residual `(P2-Slack) : S ≤ ceiling − Z` ALONE gives
`Z + S ≤ ceiling` by `linarith` (`WF6P2.slack_domination_implies_SM1` takes only `hslack`); the
char-`0` ceiling `Z ≤ ceiling` is never used by that implication.  `hZceiling` has therefore been
dropped from `WF6P2.slack_route_full`, and the redundant consumers that "supplied" it
(`slack_route_full_charzero_discharged`, `SM1_uniform_of_slack`,
`charp_residual_is_the_only_open_input`) have been removed.  The char-`0` ceiling only matters for
NON-VACUITY of the residual (it shows `ceiling − Z ≥ 0`, so `(P2-Slack)` is at least satisfiable by
`S = 0`), not for the implication.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_uniform` — `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r` UNCONDITIONALLY for every `r`
  (`gaussianEnergyBound_dyadic` unfolded).
* `SM1_uniform_at_faithful_edge` — at the faithfulness edge `Spur = 0` the bound is the char-`0`
  ceiling itself, for every `r`.

## Honest scope

Char-`0` only.  It does NOT bound `Spur_r(p)`; the `(P2-Slack)` residual stays GENUINELY OPEN (the
BGK char-`p` wall).  At the prize regime `GaussianEnergyBound` is FALSE in char-`p`
(`DCEnergyEssential`, `PairingResidualFailsAtPrize`).  No `δ*` / capacity / beyond-Johnson claim.
`CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN.  Issue #444, wf-L8.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFL8

open Nat
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ProximityGap.Frontier.CharZeroWickEnergy

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-! ## The char-`0` ceiling, UNIFORM in `r`, on the real `rEnergy` carrier -/

/-- **Char-`0` Lam–Leung ceiling, UNCONDITIONAL and UNIFORM in `r`.**  For a finset `G` of `2^k`-th
roots of unity (`k ≥ 1`) in a characteristic-`0` field (negation-closed, automatic for `μ_{2^k}`),
the `r`-fold additive energy obeys the double-factorial ceiling for **every** `r`:

> `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r`.

It is `gaussianEnergyBound_dyadic` (#407) unfolded.  (It is not needed by the slack-route implication
`(P2-Slack) ⟹ A_r ≤ ceiling_r`, which follows from the residual alone; see the module correction.) -/
theorem charzero_ceiling_uniform {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  gaussianEnergyBound_dyadic hk G hG hneg r

/-! ## Faithfulness edge -/

/-- **Faithfulness-edge sanity (`Spur = 0`), uniform in `r`.**  At the char-`0` faithfulness edge
`S = 0` (probe-confirmed through `n=16, r≤3`, where `A_r = E_r`), the bound IS the char-`0` ceiling, for every `r` — no residual needed. -/
theorem SM1_uniform_at_faithful_edge
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    (rEnergy G r : ℝ) + (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  simpa using charzero_ceiling_uniform hk G hG hneg r

end ArkLib.ProximityGap.Frontier.WFL8

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WFL8.charzero_ceiling_uniform
#print axioms ArkLib.ProximityGap.Frontier.WFL8.SM1_uniform_at_faithful_edge
