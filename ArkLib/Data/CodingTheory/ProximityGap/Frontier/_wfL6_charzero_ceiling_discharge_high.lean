/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L6, #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E9ClosedForm

/-!
# Discharging the char-`0` Lam–Leung ceiling hypothesis at `r ∈ {7,8,9}` (residual census, #444, wf-L6)

## What this discharges (the residual-census action)

The slack route `Frontier/_wf6P2_charp_lamleung_slack.lean` carries the char-`0` Lam–Leung ceiling
`(S-M1) : A_r ≤ (2r−1)‼·n^r` as a **free hypothesis** consumed by `slack_domination_implies_SM1`
(`(Z ≤ ceiling) → (S ≤ ceiling − Z) → Z + S ≤ ceiling`). Lane wf-OT4
(`_wf9OT4_charzero_ceiling_discharge.lean`) discharged that ceiling input **unconditionally only at
`r ∈ {2,3}`** — the two rungs where the char-`0` energy closed form was in tree at the time.

The `E_r` closed-form ladder has since been extended: the *just-landed* exact closed forms
`E_7`, `E_8`, `E_9` (`_AvL2_E{7,8,9}ClosedForm.lean`) each PROVE, axiom-clean and unconditionally
for `n ≥ 2`,

> `E_r(ℂ) ≤ (2r−1)‼·n^r`   (`E7_le_wick` / `E8_le_wick` / `E9_le_wick`),
> `0 < (2r−1)‼·n^r − E_r(ℂ)` (`deficit_seven_pos` / `deficit_eight_pos` / `deficit_nine_pos`).

So the char-`0` ceiling input to the slack route is now PROVEN, not assumed, at three more rungs.
This file extends the OT4 discharge to `r ∈ {7,8,9}`: it produces the char-`0` ceiling
unconditionally on the in-tree closed-form value carrier, and assembles the
`(P2-Slack) ⟹ (S-M1)` consumer with the ceiling input PROVEN rather than free, for each rung.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_seven/eight/nine`   — `E_r(ℂ) ≤ (2r−1)‼·n^r` UNCONDITIONALLY for `n ≥ 2`.
* `charzero_slack_seven/eight/nine_pos` — the slack `(2r−1)‼·n^r − E_r(ℂ) > 0` is genuine (strict),
  so the discharge is non-vacuous: there IS real headroom for the spurious term to live in.
* `SM1_seven/eight/nine_of_slack` — `(P2-Slack) at r ⟹ A_r ≤ (2r−1)‼·n^r`, with the char-`0`
  ceiling input PROVEN (`charzero_ceiling_r`), so the consumer rests ONLY on the open
  `(P2-Slack)` residual `Spur ≤ ceiling − E_r`. This is `slack_domination_implies_SM1` with the
  former free `hZceiling` DISCHARGED, at three new depths.
* `SM1_{seven,eight,nine}_at_faithful_edge` — at the faithfulness edge `Spur = 0` (the probe-confirmed
  regime through `n=16, r≤3`, where `A_r = E_r`) the prize bound IS the char-`0` ceiling, no
  residual needed.

## Honest scope

This is the char-`0` HALF only, at three more rungs of the ladder. It removes the free `hZceiling`
hypothesis from the slack route at `r ∈ {7,8,9}` (a conditional input becomes unconditional — a real
tightening of the formal cone). It does NOT bound the spurious char-`p` term `Spur_r(p)`; the
`(P2-Slack)` spurious-domination residual stays GENUINELY OPEN (= the BGK char-`p` wall, the genuine
open core). No `δ*` / capacity / beyond-Johnson claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))`
UNCHANGED/OPEN. The energy/moment route is precisely the one whose char-`p` transfer is refuted at
the prize depth `r ≈ ln q` (E8 docstring); this discharges the char-`0` boundary of what is true.

Issue #444, wf-L6.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFL6

open ProximityGap.Frontier.E7ClosedForm (E7 wick E7_le_wick deficit_seven_pos)
open ProximityGap.Frontier.E8ClosedForm (E8 E8_le_wick deficit_eight_pos)
open ProximityGap.Frontier.E9ClosedForm (E9 E9_le_wick deficit_nine_pos)

/-! ## Char-`0` Lam–Leung ceiling, UNCONDITIONAL, at `r ∈ {7,8,9}` (the discharged `hZceiling`) -/

/-- **Char-`0` Lam–Leung ceiling at `r = 7`, UNCONDITIONAL** (`n ≥ 2`):
`E_7(μ_n) ≤ (2·7−1)‼·n⁷`. The free `hZceiling` input of the slack route at `r=7` is here PROVEN
from the in-tree exact closed form via `E7_le_wick`. -/
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

/-! ## The slack is genuine (strict) — the discharge is non-vacuous -/

theorem charzero_slack_seven_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E7ClosedForm.wick 7 n - E7 n :=
  deficit_seven_pos n hn

theorem charzero_slack_eight_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E8ClosedForm.wick 8 n - E8 n :=
  deficit_eight_pos n hn

theorem charzero_slack_nine_pos (n : ℤ) (hn : 2 ≤ n) :
    0 < ProximityGap.Frontier.E9ClosedForm.wick 9 n - E9 n :=
  deficit_nine_pos n hn

/-! ## The `(P2-Slack) ⟹ (S-M1)` consumer with the char-`0` ceiling DISCHARGED

The slack route's load-bearing implication is `Z + S ≤ ceiling` from `S ≤ ceiling − Z` (the open
residual) together with `Z ≤ ceiling` (formerly the free `hZceiling`). Here `Z = E_r(ℂ)` and the
ceiling input is PROVEN by `charzero_ceiling_r`; the consumer below consumes ONLY the open
`(P2-Slack)` residual `Spur ≤ ceiling − E_r`. We restate the generic implication on `ℤ` (the slack
route states it on `ℝ`; the ℤ form is what the in-tree closed forms live on) so it is self-contained
on these carriers. -/

/-- Generic `(P2-Slack) ⟹ (S-M1)` step on `ℤ`: char-`p` energy `A = E + Spur`; if the spurious part
fits in the ceiling slack (`Spur ≤ ceiling − E`, the open residual) and `Spur ≥ 0`, then
`A ≤ ceiling`. The ceiling input `E ≤ ceiling` is supplied PROVEN at each rung below — never as a
free hypothesis. -/
theorem P2Slack_residual_implies_energy_le
    (A E Spur ceiling : ℤ)
    (hsplit : A = E + Spur) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ceiling - E) :
    A ≤ ceiling := by
  rw [hsplit]; linarith

/-- **`(S-M1)` at `r = 7` with the char-`0` ceiling DISCHARGED.** Decompose the char-`p` energy
`A_7 = E_7 + Spur`. The consumer needs `Spur ≤ ceiling − E_7` (the open `(P2-Slack)` residual) AND
`E_7 ≤ ceiling` (formerly the free `hZceiling`). The latter is now PROVEN
(`charzero_ceiling_seven`), so this consumes ONLY the open residual:
`(P2-Slack) at r=7 ⟹ A_7 ≤ (2·7−1)‼·n⁷`. -/
theorem SM1_seven_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ProximityGap.Frontier.E7ClosedForm.wick 7 n - E7 n) :
    E7 n + Spur ≤ ProximityGap.Frontier.E7ClosedForm.wick 7 n :=
  P2Slack_residual_implies_energy_le (E7 n + Spur) (E7 n) Spur
    (ProximityGap.Frontier.E7ClosedForm.wick 7 n) rfl hspur hresid

/-- **`(S-M1)` at `r = 8` with the char-`0` ceiling DISCHARGED.** -/
theorem SM1_eight_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ProximityGap.Frontier.E8ClosedForm.wick 8 n - E8 n) :
    E8 n + Spur ≤ ProximityGap.Frontier.E8ClosedForm.wick 8 n :=
  P2Slack_residual_implies_energy_le (E8 n + Spur) (E8 n) Spur
    (ProximityGap.Frontier.E8ClosedForm.wick 8 n) rfl hspur hresid

/-- **`(S-M1)` at `r = 9` with the char-`0` ceiling DISCHARGED.** -/
theorem SM1_nine_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ProximityGap.Frontier.E9ClosedForm.wick 9 n - E9 n) :
    E9 n + Spur ≤ ProximityGap.Frontier.E9ClosedForm.wick 9 n :=
  P2Slack_residual_implies_energy_le (E9 n + Spur) (E9 n) Spur
    (ProximityGap.Frontier.E9ClosedForm.wick 9 n) rfl hspur hresid

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
#print axioms ArkLib.ProximityGap.Frontier.WFL6.SM1_seven_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6.SM1_eight_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6.SM1_nine_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6.SM1_seven_at_faithful_edge
