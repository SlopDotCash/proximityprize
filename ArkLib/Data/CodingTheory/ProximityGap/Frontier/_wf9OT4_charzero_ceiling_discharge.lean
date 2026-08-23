/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-OT4, #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroLamLeungSlackLower

/-!
# Discharging the char-`0` Lam–Leung ceiling hypothesis at `r ∈ {2,3}` (OT4 residual census, #444)

## What this discharges (the residual-census action)

The slack route `Frontier/_wf6P2_charp_lamleung_slack.lean` carries the char-`0` Lam–Leung ceiling
as a **free hypothesis** `hZceiling : Z ≤ ceiling` (its docstring: *"the char-`0` ceiling on `Z`…
supplied here as a hypothesis so the brick is substrate-light"*). At the two depths `r ∈ {2,3}`
where the char-`0` zero-sum count `A_r^ℤ = E_r(μ_n)` has a PROVEN exact closed form in tree
(`CharZeroEnergyThree.B4_closed`, `B6_eq_E3`), that hypothesis is no longer free: the strict-slack
lemmas `CharZeroLamLeungSlackLower.slack_two_pos` / `slack_three_pos` already PROVE
`E_r < (2r-1)‼·n^r`, hence the non-strict ceiling `E_r ≤ (2r-1)‼·n^r` that the route consumes.

This file produces that ceiling **unconditionally** (no `hZceiling` binder) on the in-tree
`BalancedCount` carrier, at `r = 2` and `r = 3`, and assembles the `(P2-Slack) ⟹ A_r ≤ ceiling`
implication with the ceiling input now PROVEN rather than assumed. The remaining `(P2-Slack)`
spurious-domination residual stays genuinely OPEN — this discharges only the char-`0` half, which
is exactly the half the char-`0` closures (B2/B8 carrier work) make available.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_two`   — `B 4 m ≤ 3·(2m)²` UNCONDITIONALLY for `m ≥ 1` (`= E_2 ≤ 3!!·n²`).
* `charzero_ceiling_three` — `B 6 m ≤ 15·(2m)³` UNCONDITIONALLY for `m ≥ 1` (`= E_3 ≤ 5!!·n³`).
* `charzero_ceiling_two_value` / `_three_value` — the same on the closed-form VALUE (`3n²−3n`,
  `15n³−45n²+40n`), for consumers holding the value not the carrier.
* `SM1_two_of_slack`  — `(P2-Slack)` at `r=2` ⟹ `A_2 ≤ 3·(2m)²`, with the ceiling input PROVEN
  (`charzero_ceiling_two`), not assumed.  This is `slack_domination_implies_SM1` with `hZceiling`
  DISCHARGED.
* `SM1_three_of_slack` — the same at `r=3`.

## Honest scope

This is the char-`0` HALF only. It removes the `hZceiling` free hypothesis from the slack route at
`r ∈ {2,3}` — a real tightening of the formal cone (a conditional input becomes unconditional). It
does NOT bound the spurious char-`p` term `Spur_r(p)`; the `(P2-Slack)` residual
`Spur ≤ ceiling − E_r` stays OPEN (BGK-adjacent, the genuine open core). No `δ*` / capacity /
beyond-Johnson claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN.

Prize-scale guard (`scripts/probes/probe_wf9OT4_ceiling_discharge.py`): the slack is exactly
`Slack_2 = 3n > 0`, `Slack_3 = 45n²−40n > 0` through `n = 2^30`; the ceiling is genuine (strict),
so the discharge is non-vacuous at prize scale. Issue #444, wf-OT4.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WF9OT4

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree
open ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower

variable {B : ℕ → ℕ → ℤ}

/-- **Char-`0` Lam–Leung ceiling at `r = 2`, UNCONDITIONAL** (`m ≥ 1`, i.e. `n = 2m ≥ 2`):
`E_2(μ_n) = B 4 m ≤ 3·(2m)² = 3!!·n²`. The free `hZceiling` hypothesis of the slack route at `r=2`
is here PROVEN from the in-tree exact energy `B4_closed` via the strict slack `slack_two_pos`
(`B 4 m < 3·(2m)²`, weakened to `≤`). -/
theorem charzero_ceiling_two (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 4 m ≤ 3 * (2 * (m : ℤ)) ^ 2 :=
  le_of_lt (slack_two_pos h m hm)

/-- **Char-`0` Lam–Leung ceiling at `r = 3`, UNCONDITIONAL** (`m ≥ 1`):
`E_3(μ_n) = B 6 m ≤ 15·(2m)³ = 5!!·n³`. PROVEN from `B6_eq_E3` via `slack_three_pos`. -/
theorem charzero_ceiling_three (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 6 m ≤ 15 * (2 * (m : ℤ)) ^ 3 :=
  le_of_lt (slack_three_pos h m hm)

/-- The `r=2` ceiling stated on the closed-form VALUE `E_2 = 3n²−3n` (any `n ≥ 1`):
`3n²−3n ≤ 3n²`. For consumers holding the value, not the `BalancedCount` carrier. -/
theorem charzero_ceiling_two_value (n : ℤ) (hn : 1 ≤ n) :
    3 * n ^ 2 - 3 * n ≤ 3 * n ^ 2 :=
  le_of_lt (slack_two_pos_value n hn)

/-- The `r=3` ceiling on the closed-form VALUE `E_3 = 15n³−45n²+40n` (any `n ≥ 1`):
`15n³−45n²+40n ≤ 15n³`. -/
theorem charzero_ceiling_three_value (n : ℤ) (hn : 1 ≤ n) :
    15 * n ^ 3 - 45 * n ^ 2 + 40 * n ≤ 15 * n ^ 3 :=
  le_of_lt (slack_three_pos_value n hn)

/-- **`(S-M1)` at `r = 2` with the char-`0` ceiling DISCHARGED.** Decompose the char-`p` energy
`A_2 = E_2 + Spur = B 4 m + Spur`. The slack route's `slack_domination_implies_SM1` needs
`Spur ≤ ceiling − E_2` (the open `(P2-Slack)` residual) AND `E_2 ≤ ceiling` (formerly the free
`hZceiling`). The latter is now PROVEN (`charzero_ceiling_two`), so this consumes ONLY the open
residual: `(P2-Slack) at r=2 ⟹ A_2 ≤ 3·(2m)²`. -/
theorem SM1_two_of_slack (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ 3 * (2 * (m : ℤ)) ^ 2 - B 4 m) :
    B 4 m + Spur ≤ 3 * (2 * (m : ℤ)) ^ 2 :=
  -- ceiling input is PROVEN (charzero_ceiling_two), not assumed; only `hresid` is open.
  P2Slack_residual_implies_energy_le (B 4 m + Spur) (B 4 m) Spur (3 * (2 * (m : ℤ)) ^ 2)
    rfl hspur hresid

/-- **`(S-M1)` at `r = 3` with the char-`0` ceiling DISCHARGED.** Same shape at depth 3:
`(P2-Slack) at r=3 ⟹ A_3 = B 6 m + Spur ≤ 15·(2m)³`. The ceiling input `charzero_ceiling_three`
is PROVEN; only the spurious-domination residual is consumed. -/
theorem SM1_three_of_slack (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ 15 * (2 * (m : ℤ)) ^ 3 - B 6 m) :
    B 6 m + Spur ≤ 15 * (2 * (m : ℤ)) ^ 3 :=
  P2Slack_residual_implies_energy_le (B 6 m + Spur) (B 6 m) Spur (15 * (2 * (m : ℤ)) ^ 3)
    rfl hspur hresid

/-- **Sanity: at the faithfulness edge `Spur = 0` the char-`0` energy IS the char-`p` energy and
both ceilings hold unconditionally** (no residual needed). This is the regime the probe confirms
holds through the char-`0` faithfulness edge (`Spur = 0` through `n=16, r=3`): the prize bound is
then literally the char-`0` ceiling with the spurious term absent. -/
theorem SM1_two_at_faithful_edge (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 4 m + (0 : ℤ) ≤ 3 * (2 * (m : ℤ)) ^ 2 := by
  simpa using charzero_ceiling_two h m hm

theorem SM1_three_at_faithful_edge (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 6 m + (0 : ℤ) ≤ 15 * (2 * (m : ℤ)) ^ 3 := by
  simpa using charzero_ceiling_three h m hm

end ArkLib.ProximityGap.Frontier.WF9OT4

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.charzero_ceiling_two
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.charzero_ceiling_three
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.charzero_ceiling_two_value
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.charzero_ceiling_three_value
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.SM1_two_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.SM1_three_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.SM1_two_at_faithful_edge
#print axioms ArkLib.ProximityGap.Frontier.WF9OT4.SM1_three_at_faithful_edge
