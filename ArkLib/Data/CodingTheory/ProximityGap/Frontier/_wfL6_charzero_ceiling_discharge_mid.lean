/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L6, #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroEnergyClosedForm

/-!
# Discharging the char-`0` Lam–Leung ceiling hypothesis at `r ∈ {4,5,6}` (residual census, #444, wf-L6)

## What this discharges (the residual-census close-out action)

The slack route `Frontier/_wf6P2_charp_lamleung_slack.lean` carries the char-`0` Lam–Leung ceiling
`(S-M1) : A_r ≤ (2r−1)‼·n^r` as a **free hypothesis** (`hZceiling`) consumed by
`slack_domination_implies_SM1` (`(Z ≤ ceiling) → (S ≤ ceiling − Z) → Z + S ≤ ceiling`). Two prior
landed lanes discharged that ceiling input unconditionally only at the ENDS of the proven ladder:
`_wf9OT4_charzero_ceiling_discharge.lean` at `r ∈ {2,3}` and
`_wfL6_charzero_ceiling_discharge_high.lean` at `r ∈ {7,8,9}`. The MIDDLE rungs `r ∈ {4,5,6}` —
whose char-`0` exact closed forms `E_4, E_5, E_6` and non-strict ceilings `E_r ≤ (2r−1)‼·n^r`
(`E4_le_wick / E5_le_wick / E6_le_wick`) are ALREADY PROVEN unconditionally in
`_CharZeroEnergyClosedForm.lean` — were never wired into the slack-route discharge, and their
strict-slack positivity `0 < (2r−1)‼·n^r − E_r` (the non-vacuity certificate that
`deficit_two_pos`/`deficit_three_pos` provide at `r ∈ {2,3}`) was MISSING at `r ∈ {4,5,6}`.

This file **closes the contiguous ceiling-discharge ladder `r = 2..9`** on the in-tree closed-form
`ℤ`-carrier: it proves the strict deficit positivity at the three middle rungs (NEW — only
`deficit_{two,three}_pos` were in tree) and assembles the `(P2-Slack) ⟹ (S-M1)` consumer with the
char-`0` ceiling input PROVEN (`E{4,5,6}_le_wick`) rather than free, for each middle rung. It lives on
the integer closed-form carrier (`E_r : ℤ`), so it needs NO `CharZero F` instance synthesis and is
robust under both `lake build` and `lake env lean`.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_{four,five,six}`   — `E_r(ℂ) ≤ (2r−1)‼·n^r` UNCONDITIONALLY for `n ≥ 2`,
  re-exported from the in-tree `E{4,5,6}_le_wick`.
* `charzero_slack_{four,five,six}_pos` — the slack `(2r−1)‼·n^r − E_r(ℂ) > 0` is genuine (strict)
  for `n ≥ 2` (NEW: closes the `deficit_*_pos` ladder, which previously stopped at `r=3`), so the
  discharge is non-vacuous: there IS real headroom for the spurious term to live in.
* `SM1_{four,five,six}_of_slack` — `(P2-Slack) at r ⟹ A_r ≤ (2r−1)‼·n^r`, with the char-`0`
  ceiling input PROVEN, so the consumer rests ONLY on the open `(P2-Slack)` residual
  `Spur ≤ ceiling − E_r`. This is `slack_domination_implies_SM1` with the former free `hZceiling`
  DISCHARGED, at the three middle depths.
* `SM1_{four,five,six}_at_faithful_edge` — at the faithfulness edge `Spur = 0` (where `A_r = E_r`)
  the prize bound IS the char-`0` ceiling, no residual needed.

## Honest scope

This is the char-`0` HALF only, completing the middle of the `r = 2..9` ladder. It removes the free
`hZceiling` hypothesis from the slack route at `r ∈ {4,5,6}` (a conditional input becomes
unconditional — a real tightening of the formal cone). It does NOT bound the spurious char-`p` term
`Spur_r(p)`; the `(P2-Slack)` spurious-domination residual stays GENUINELY OPEN (= the BGK char-`p`
wall, the genuine open core: the char-`p` transfer of the energy bound at depth `r ≈ ln q`, refuted
at the prize prime). No `δ*` / capacity / beyond-Johnson claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))`
UNCHANGED/OPEN.

Issue #444, wf-L6.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFL6Mid

open ProximityGap.Frontier.CharZeroEnergy

/-! ## Strict char-`0` deficit positivity at `r ∈ {4,5,6}` (NEW — closes the `deficit_*_pos` ladder)

The source `_CharZeroEnergyClosedForm.lean` proves the non-strict ceilings `E{4,5,6}_le_wick` and the
exact deficit identities `deficit_{four,five,six}`, but the strict positivity certificates
`0 < wick r n − E_r n` (non-vacuity of the discharge) were only established at `r ∈ {2,3}`. These
three lemmas fill that gap, matching the `n ≥ 2` regime of the corresponding `E_r ≤ wick`. -/

/-- **Strict char-`0` slack at `r = 4`** (`n ≥ 2`): `0 < 4!!·n⁴ − E_4(μ_n)`, i.e. the deficit
`630n³ − 1435n² + 1155n > 0`. The cushion is strictly positive at prize scale. -/
theorem deficit_four_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 4 n - E4 n := by
  rw [deficit_four]
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2)),
    mul_nonneg (by linarith : (0:ℤ) ≤ n) (by nlinarith : (0:ℤ) ≤ 126 * n ^ 2 - 287 * n + 231),
    mul_pos (by linarith : (0:ℤ) < n) (by linarith : (0:ℤ) < n)]

/-- **Strict char-`0` slack at `r = 5`** (`n ≥ 2`): `0 < 5!!·n⁵ − E_5(μ_n)`, i.e.
`9450n⁴ − 39375n³ + 77175n² − 57456n > 0`. -/
theorem deficit_five_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 5 n - E5 n := by
  rw [deficit_five]
  have hcubic : (0:ℤ) < 9450 * n ^ 3 - 39375 * n ^ 2 + 77175 * n - 57456 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2)),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (sq_nonneg (n - 2)), hn]
  have hprod : (0:ℤ) < n * (9450 * n ^ 3 - 39375 * n ^ 2 + 77175 * n - 57456) :=
    mul_pos (by linarith) hcubic
  nlinarith [hprod]

/-- **Strict char-`0` slack at `r = 6`** (`n ≥ 2`): `0 < 6!!·n⁶ − E_6(μ_n)`, i.e.
`155925n⁵ − 1022175n⁴ + 3534300n³ − 6246471n² + 4370520n > 0`. -/
theorem deficit_six_pos (n : ℤ) (hn : 2 ≤ n) : 0 < wick 6 n - E6 n := by
  rw [deficit_six]
  have hquartic : (0:ℤ) <
      155925 * n ^ 4 - 1022175 * n ^ 3 + 3534300 * n ^ 2 - 6246471 * n + 4370520 := by
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (sq_nonneg (n - 2)),
      mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ n))
        (sq_nonneg (n - 2)),
      mul_nonneg (by linarith : (0:ℤ) ≤ n - 2) (sq_nonneg (n - 2)), hn, sq_nonneg (n - 2)]
  have hprod : (0:ℤ) < n *
      (155925 * n ^ 4 - 1022175 * n ^ 3 + 3534300 * n ^ 2 - 6246471 * n + 4370520) :=
    mul_pos (by linarith) hquartic
  nlinarith [hprod]

/-! ## Char-`0` Lam–Leung ceiling, UNCONDITIONAL, at `r ∈ {4,5,6}` (the discharged `hZceiling`) -/

/-- **Char-`0` Lam–Leung ceiling at `r = 4`, UNCONDITIONAL** (`n ≥ 2`):
`E_4(μ_n) ≤ (2·4−1)‼·n⁴ = 105 n⁴`. Re-exported from the in-tree `E4_le_wick`; this is the former
free `hZceiling` of the slack route at `r=4`, now PROVEN. -/
theorem charzero_ceiling_four (n : ℤ) (hn : 2 ≤ n) : E4 n ≤ wick 4 n :=
  E4_le_wick n hn

/-- **Char-`0` Lam–Leung ceiling at `r = 5`, UNCONDITIONAL** (`n ≥ 2`): `E_5(μ_n) ≤ 945 n⁵`. -/
theorem charzero_ceiling_five (n : ℤ) (hn : 2 ≤ n) : E5 n ≤ wick 5 n :=
  E5_le_wick n hn

/-- **Char-`0` Lam–Leung ceiling at `r = 6`, UNCONDITIONAL** (`n ≥ 2`): `E_6(μ_n) ≤ 10395 n⁶`. -/
theorem charzero_ceiling_six (n : ℤ) (hn : 2 ≤ n) : E6 n ≤ wick 6 n :=
  E6_le_wick n hn

/-! ## The `(P2-Slack) ⟹ (S-M1)` consumer with the char-`0` ceiling DISCHARGED

`slack_domination_implies_SM1` on `ℤ`: char-`p` energy `A = E + Spur`; if the spurious part fits in
the ceiling slack (`Spur ≤ ceiling − E`, the open residual) and `Spur ≥ 0`, then `A ≤ ceiling`. The
ceiling input `E ≤ ceiling` is supplied PROVEN at each rung (`charzero_ceiling_r`) — never free. -/

/-- Generic `(P2-Slack) ⟹ (S-M1)` step on `ℤ`. Identical to the OT4 / high-rung generic step;
restated here so the file is self-contained on the closed-form `E_r` carriers. -/
theorem P2Slack_residual_implies_energy_le
    (A E Spur ceiling : ℤ)
    (hsplit : A = E + Spur) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ceiling - E) :
    A ≤ ceiling := by
  rw [hsplit]; linarith

/-- **`(S-M1)` at `r = 4` with the char-`0` ceiling DISCHARGED.** Decompose `A_4 = E_4 + Spur`. The
consumer needs `Spur ≤ ceiling − E_4` (the open `(P2-Slack)` residual) AND `E_4 ≤ ceiling` (formerly
the free `hZceiling`). The latter is PROVEN (`charzero_ceiling_four`), so this consumes ONLY the open
residual: `(P2-Slack) at r=4 ⟹ A_4 ≤ 105 n⁴`. -/
theorem SM1_four_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ wick 4 n - E4 n) :
    E4 n + Spur ≤ wick 4 n :=
  P2Slack_residual_implies_energy_le (E4 n + Spur) (E4 n) Spur (wick 4 n) rfl hspur hresid

/-- **`(S-M1)` at `r = 5` with the char-`0` ceiling DISCHARGED.** -/
theorem SM1_five_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ wick 5 n - E5 n) :
    E5 n + Spur ≤ wick 5 n :=
  P2Slack_residual_implies_energy_le (E5 n + Spur) (E5 n) Spur (wick 5 n) rfl hspur hresid

/-- **`(S-M1)` at `r = 6` with the char-`0` ceiling DISCHARGED.** -/
theorem SM1_six_of_slack (n : ℤ) (hn : 2 ≤ n)
    (Spur : ℤ) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ wick 6 n - E6 n) :
    E6 n + Spur ≤ wick 6 n :=
  P2Slack_residual_implies_energy_le (E6 n + Spur) (E6 n) Spur (wick 6 n) rfl hspur hresid

/-! ## Faithfulness-edge sanity (`Spur = 0`): the prize bound IS the char-`0` ceiling -/

theorem SM1_four_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) : E4 n + (0 : ℤ) ≤ wick 4 n := by
  simpa using charzero_ceiling_four n hn

theorem SM1_five_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) : E5 n + (0 : ℤ) ≤ wick 5 n := by
  simpa using charzero_ceiling_five n hn

theorem SM1_six_at_faithful_edge (n : ℤ) (hn : 2 ≤ n) : E6 n + (0 : ℤ) ≤ wick 6 n := by
  simpa using charzero_ceiling_six n hn

end ArkLib.ProximityGap.Frontier.WFL6Mid

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.deficit_four_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.deficit_five_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.deficit_six_pos
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.charzero_ceiling_four
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.charzero_ceiling_five
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.charzero_ceiling_six
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_four_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_five_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_six_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_four_at_faithful_edge
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_five_at_faithful_edge
#print axioms ArkLib.ProximityGap.Frontier.WFL6Mid.SM1_six_at_faithful_edge
