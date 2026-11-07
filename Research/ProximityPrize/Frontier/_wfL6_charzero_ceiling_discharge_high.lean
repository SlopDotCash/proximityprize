/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L6, #444)
-/
import Research.ProximityPrize.Frontier._AvL2_E7ClosedForm
import Research.ProximityPrize.Frontier._AvL2_E8ClosedForm
import Research.ProximityPrize.Frontier._AvL2_E9ClosedForm

/-!
# Char-`0` Lam–Leung ceilings and strict deficits at `r ∈ {7,8,9}` (residual census, #444, wf-L6)

## What this file proves

The exact closed forms `E_7`, `E_8`, `E_9` (`_AvL2_E{7,8,9}ClosedForm.lean`) each prove, axiom-clean
and unconditionally for `n ≥ 2`,

> `E_r(ℂ) ≤ (2r−1)‼·n^r`   (`E7_le_wick` / `E8_le_wick` / `E9_le_wick`),
> `0 < (2r−1)‼·n^r − E_r(ℂ)` (`deficit_seven_pos` / `deficit_eight_pos` / `deficit_nine_pos`).

This file re-exports them at `r ∈ {7,8,9}`.

## Correction (audit 2026-10-28, CW-B18-08)

An earlier version of this file framed these ceilings as "discharging the free `hZceiling`
hypothesis of the slack route".  That was wrong: the slack residual `(P2-Slack) : Spur ≤ ceiling − E_r`
ALONE gives `E_r + Spur ≤ ceiling` by `linarith` (`WF6P2.slack_domination_implies_SM1` takes only the
residual, and `hZceiling` has been dropped from `WF6P2.slack_route_full`).  The char-`0` ceiling is
not a load-bearing input of that implication; the per-rung `(P2-Slack) ⟹ (S-M1)` consumers that
"supplied" it were redundant and have been removed.  What remains meaningful is the ceiling itself and
the STRICT deficit positivity, which certifies that `(P2-Slack)` is non-vacuous (there is real
headroom `ceiling − E_r > 0` for `Spur`).

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_seven/eight/nine`   — `E_r(ℂ) ≤ (2r−1)‼·n^r` UNCONDITIONALLY for `n ≥ 2`.
* `charzero_slack_seven/eight/nine_pos` — the slack `(2r−1)‼·n^r − E_r(ℂ) > 0` is genuine (strict),
  so the `(P2-Slack)` residual is non-vacuous: there IS real headroom for the spurious term to live in.
* `SM1_{seven,eight,nine}_at_faithful_edge` — at the faithfulness edge `Spur = 0` (the probe-confirmed
  regime through `n=16, r≤3`, where `A_r = E_r`) the prize bound IS the char-`0` ceiling, no
  residual needed.

## Honest scope

Char-`0` only.  It does NOT bound the spurious char-`p` term `Spur_r(p)`; the `(P2-Slack)` residual
stays GENUINELY OPEN (the BGK char-`p` wall).  No `δ*` / capacity / beyond-Johnson claim.
`CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN.  The energy/moment route is precisely the one whose
char-`p` transfer is refuted at the prize depth `r ≈ ln q` (E8 docstring).

Issue #444, wf-L6.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFL6

open ProximityGap.Frontier.E7ClosedForm (E7 wick E7_le_wick deficit_seven_pos)
open ProximityGap.Frontier.E8ClosedForm (E8 E8_le_wick deficit_eight_pos)
open ProximityGap.Frontier.E9ClosedForm (E9 E9_le_wick deficit_nine_pos)

/-! ## Char-`0` Lam–Leung ceiling, UNCONDITIONAL, at `r ∈ {7,8,9}` -/

/-- **Char-`0` Lam–Leung ceiling at `r = 7`, UNCONDITIONAL** (`n ≥ 2`):
`E_7(μ_n) ≤ (2·7−1)‼·n⁷`. PROVEN from the in-tree exact closed form via `E7_le_wick`. -/
theorem charzero_ceiling_seven (n : ℤ) (hn : 2 ≤ n) :
    E7 n ≤ ProximityGap.Frontier.E7ClosedForm.wick 7 n :=
  E7_le_wick n hn

/-- **Char-`0` Lam–Leung ceiling at `r = 8`, UNCONDITIONAL** (`n ≥ 2`):
`E_8(μ_n) ≤ (2·8−1)‼·n⁸ = 2027025 n⁸`. PROVEN from `E8_le_wick`. -/
theorem charzero_ceiling_eight (n : ℤ) (hn : 2 ≤ n) :
    E8 n ≤ ProximityGap.Frontier.E8ClosedForm.wick 8 n :=
  E8_le_wick n hn

/-- **Char-`0` Lam–Leung ceiling at `r = 9`, UNCONDITIONAL** (`n ≥ 2`):
`E_9(μ_n) ≤ (2·9−1)‼·n⁹`. PROVEN from `E9_le_wick`. -/
theorem charzero_ceiling_nine (n : ℤ) (hn : 2 ≤ n) :
    E9 n ≤ ProximityGap.Frontier.E9ClosedForm.wick 9 n :=
  E9_le_wick n hn

/-! ## The slack is genuine (strict) — the `(P2-Slack)` residual is non-vacuous -/

theorem charzero_slack_seven_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E7ClosedForm.wick 7 n - E7 n :=
  deficit_seven_pos n hn

theorem charzero_slack_eight_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E8ClosedForm.wick 8 n - E8 n :=
  deficit_eight_pos n hn

theorem charzero_slack_nine_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E9ClosedForm.wick 9 n - E9 n :=
  deficit_nine_pos n hn

/-! ## Faithfulness-edge sanity (`Spur = 0`): the prize bound IS the char-`0` ceiling -/

theorem SM1_seven_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) :
    E7 n + (0 : ℤ) ≤ ProximityGap.Frontier.E7ClosedForm.wick 7 n := by
  simpa using charzero_ceiling_seven n hn

theorem SM1_eight_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) :
    E8 n + (0 : ℤ) ≤ ProximityGap.Frontier.E8ClosedForm.wick 8 n := by
  simpa using charzero_ceiling_eight n hn

theorem SM1_nine_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) :
    E9 n + (0 : ℤ) ≤ ProximityGap.Frontier.E9ClosedForm.wick 9 n := by
  simpa using charzero_ceiling_nine n hn

end ArkLib.ProximityGap.Frontier.WFL6

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_ceiling_seven
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_ceiling_eight
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_ceiling_nine
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_slack_seven_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_slack_eight_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6.charzero_slack_nine_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6.SM1_seven_at_faithful_edge
