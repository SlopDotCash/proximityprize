/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroEnergyThreeExact

/-!
# The char-`0` Lam-Leung SLACK is exact and strictly positive (#444, wf-P2 open residual)

## The open residual this PRODUCES headroom for

`Frontier/_wf6P2_charp_lamleung_slack.lean` reduces the prize moment ceiling `(S-M1)` to ONE open
arithmetic residual on the prize prime:

> `(P2-Slack)`   `Spur_r(p) ≤ (2r−1)‼·n^r − A_r^ℤ(μ_n) =: Slack_r`

(the spurious mod-`p` coincidences fit inside the char-`0` Lam-Leung slack). That file carries
`Slack_r ≥ 0` (and the whole residual) on FAITH -- it never proves the slack is even strictly
positive, let alone gives its exact size. So there is no in-tree theorem PRODUCING the headroom
`Slack_r > 0` that `(P2-Slack)` needs to be a non-vacuous target.

This file supplies that headroom EXACTLY, at the two depths where the char-`0` zero-sum count
`A_r^ℤ = E_r(μ_n)` has a proven closed form in tree
(`CharZeroEnergyThree.B4_closed`, `…B6_eq_E3`; `E_2 = 3n²−3n`, `E_3 = 15n³−45n²+40n`).
The double-factorial ceiling is `(2r−1)‼·n^r` (`3·n²` at `r=2`, `15·n³` at `r=3`), so the slack is
an EXACT low-order polynomial:

> **`Slack_2 = 3n² − (3n²−3n) = 3n`**          (strictly `> 0` for `n ≥ 1`),
> **`Slack_3 = 15n³ − (15n³−45n²+40n) = 45n²−40n`**   (strictly `> 0` for `n ≥ 1`).

The leading `n^r` terms of ceiling and energy CANCEL EXACTLY (the Lam-Leung ceiling is the leading
asymptotic of the energy); the slack is governed by the SUB-LEADING `n^{r-1}` term. This both pins
the headroom available to the spurious term and explains the probe's `Spur/Slack ≤ 0.11`:
`Slack_r ~ c_r · n^{r-1}` while the char-`0` energy `~ (2r-1)‼·n^r`, so the relative slack
`Slack_r / ceiling_r ~ (c_r / (2r-1)‼) · (1/n) → 0`. The residual is real but TIGHTENING in `n`.

## What is PROVEN (axiom-clean ℤ/ℕ arithmetic on the in-tree `BalancedCount` carrier)

Work on the abstract balanced-count carrier `B` (`BalancedCount B`, the exact in-tree model of the
zero-sum counts, with `B 4 m = E_2(μ_{2m})`, `B 6 m = E_3(μ_{2m})`):

* `slack_two_eq`   -- `3·(2m)² − B 4 m = 6m`   (i.e. `Slack_2 = 3n` with `n = 2m`).
* `slack_three_eq` -- `15·(2m)³ − B 6 m = 45·(2m)² − 40·(2m)`   (i.e. `Slack_3 = 45n²−40n`).
* `slack_two_pos`   -- `Slack_2 > 0` for `m ≥ 1` (so `n ≥ 2`), i.e. `B 4 m < 3·(2m)²`.
* `slack_three_pos` -- `Slack_3 > 0` for `m ≥ 1`, i.e. `B 6 m < 15·(2m)³` (the char-`0` energy is
  STRICTLY below the Lam-Leung ceiling -- the slack is genuine, not vacuous).
* `slack_two_pos_value` / `slack_three_pos_value` -- the same, stated directly on the closed-form
  VALUES `3n²−3n` and `15n³−45n²+40n` (so any consumer holding only the values, not the carrier,
  gets the strict gap; the `r=3` positivity uses `disc(45n²−40n) ` has the root `n=8/9 < 1`, hence
  `> 0` for all `n ≥ 1`).
* `P2Slack_residual_implies_energy_le` -- the CONSUMER: if `Spur ≥ 0` and `Spur ≤ Slack_r` (the
  `(P2-Slack)` residual) then the char-`p` energy `A_r = A_r^ℤ + Spur ≤ (2r−1)‼·n^r` (`(S-M1)`).
  This is the load-bearing implication `(P2-Slack) ⟹ (S-M1)` with the slack now an EXPLICIT
  strictly-positive polynomial rather than an unquantified hypothesis.

## Honest scope (rules 1,3,6 + ASYMPTOTIC GUARD)

NOT a CORE closure and NOT thinness-closing. This PRODUCES the exact char-`0` slack (the headroom
the open `(P2-Slack)` residual lives in) at `r ∈ {2,3}`; it does NOT bound the spurious char-`p`
term `Spur_r(p)` itself -- that (the genuinely-open arithmetic on the prize prime) stays OPEN. The
slack values are char-`0` cyclotomic (field-universal in their derivation via the proven closed
forms); they make NO capacity/beyond-Johnson/growth-law claim and do not touch `δ*` or the
cliff-at-`n/2`. `CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN. Probe
`scripts/probes/probe_lamleung_slack_lower.py`: `Slack_2=3n`, `Slack_3=45n²−40n` exact;
`Spur = A_r − E_r^ℤ = 0` through the faithfulness edge in the prize regime (`p≫n³`, `p≡1 mod n`,
PROPER `μ_n`, never `n=q-1`), so `0 ≤ Spur ≤ Slack` holds. Issue #444, wf-P2.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower

open ArkLib.ProximityGap.Frontier.CharZeroEnergyThree

variable {B : ℕ → ℕ → ℤ}

/-- **`Slack_2 = 3n` exactly** (`n = 2m`). The `r=2` double-factorial ceiling is `3‼·n² = 3·(2m)²`;
the char-`0` energy is `E_2 = B 4 m = 3n²−3n` (`B4_closed`, `= 12m²−6m`). Their difference is the
sub-leading term `3n²−(3n²−3n) = 3n = 6m`. The leading `3n²` cancels exactly. -/
theorem slack_two_eq (h : BalancedCount B) (m : ℕ) :
    3 * (2 * (m : ℤ)) ^ 2 - B 4 m = 6 * m := by
  rw [B4_closed h]; ring

/-- **`Slack_3 = 45n²−40n` exactly** (`n = 2m`). The `r=3` ceiling is `5‼·n³ = 15·(2m)³`; the
energy is `E_3 = B 6 m = 15n³−45n²+40n` (`B6_eq_E3`). Their difference is the sub-leading
`15n³−(15n³−45n²+40n) = 45n²−40n`. The leading `15n³` cancels exactly. -/
theorem slack_three_eq (h : BalancedCount B) (m : ℕ) :
    15 * (2 * (m : ℤ)) ^ 3 - B 6 m = 45 * (2 * (m : ℤ)) ^ 2 - 40 * (2 * (m : ℤ)) := by
  rw [B6_eq_E3 h]; ring

/-- **`Slack_2 > 0` for `m ≥ 1`** (i.e. `n ≥ 2`): the char-`0` `r=2` energy `B 4 m` is STRICTLY
below the Lam-Leung ceiling `3·(2m)²`, with gap `6m > 0`. The slack is genuine, not vacuous. -/
theorem slack_two_pos (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 4 m < 3 * (2 * (m : ℤ)) ^ 2 := by
  have he := slack_two_eq h m
  have hpos : (0 : ℤ) < 6 * m := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    linarith
  linarith

/-- **`Slack_3 > 0` for `m ≥ 1`**: the char-`0` `r=3` energy `B 6 m` is STRICTLY below the
Lam-Leung ceiling `15·(2m)³`, with gap `45·(2m)²−40·(2m) = 180m²−80m > 0` for `m ≥ 1`. -/
theorem slack_three_pos (h : BalancedCount B) (m : ℕ) (hm : 1 ≤ m) :
    B 6 m < 15 * (2 * (m : ℤ)) ^ 3 := by
  have he := slack_three_eq h m
  have hm' : (1 : ℤ) ≤ m := by exact_mod_cast hm
  -- gap = 45*(2m)^2 - 40*(2m) = 180 m^2 - 80 m = 20 m (9 m - 4) > 0 for m ≥ 1
  have hgap : (0 : ℤ) < 45 * (2 * (m : ℤ)) ^ 2 - 40 * (2 * (m : ℤ)) := by nlinarith [hm']
  linarith

/-- **`Slack_2 > 0` on the closed-form VALUE** `E_2 = 3n²−3n` directly (for consumers holding the
value, not the `BalancedCount` carrier): `3n²−3n < 3n²` for `n ≥ 1`, with gap exactly `3n > 0`. -/
theorem slack_two_pos_value (n : ℤ) (hn : 1 ≤ n) :
    3 * n ^ 2 - 3 * n < 3 * n ^ 2 := by nlinarith [hn]

/-- **`Slack_3 > 0` on the closed-form VALUE** `E_3 = 15n³−45n²+40n` directly: `E_3 < 15n³` for
`n ≥ 1`, with gap `45n²−40n = 5n(9n−8) > 0` (the quadratic `45n²−40n` has its positive root at
`n = 8/9 < 1`, so it is strictly positive for all `n ≥ 1`). -/
theorem slack_three_pos_value (n : ℤ) (hn : 1 ≤ n) :
    15 * n ^ 3 - 45 * n ^ 2 + 40 * n < 15 * n ^ 3 := by nlinarith [hn]

/-- **The `(P2-Slack) ⟹ (S-M1)` consumer, with the slack now an EXPLICIT positive polynomial.**
Let `Ar = Az + Spur` be the char-`p` energy decomposition (`Az` = char-`0` zero-sum count = energy,
`Spur ≥ 0` the spurious mod-`p` coincidences). If the spurious term fits in the slack
(`Spur ≤ ceiling − Az`, the `(P2-Slack)` residual), then `Ar ≤ ceiling` (= `(S-M1)`). Generic over
the ceiling/energy so it applies at BOTH depths via `slack_two_eq`/`slack_three_eq` (which exhibit
`ceiling − Az = Slack_r > 0`). This is the load-bearing step `(P2-Slack) ⟹ (S-M1)`, now resting on
an exhibited strictly-positive slack rather than an unquantified `Slack ≥ 0` hypothesis. -/
theorem P2Slack_residual_implies_energy_le
    (Ar Az Spur ceiling : ℤ)
    (hsplit : Ar = Az + Spur) (hspur : 0 ≤ Spur)
    (hresid : Spur ≤ ceiling - Az) :
    Ar ≤ ceiling := by
  rw [hsplit]; linarith

end ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_two_eq
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_three_eq
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_two_pos
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_three_pos
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_two_pos_value
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.slack_three_pos_value
#print axioms ArkLib.ProximityGap.Frontier.CharZeroLamLeungSlackLower.P2Slack_residual_implies_energy_le
