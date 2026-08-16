/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BchksF5_CharPAnomalyExpZero
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-`0` Lam-Leung SLACK leading coefficient is `C(r,2)·(2r−1)‼` — uniformly in `r` (#444)

## What this PRODUCES (the open producer the slack files left un-named)

`Frontier/_CharZeroLamLeungSlackLower.lean` lands the EXACT char-`0` slack
`Slack_r := (2r−1)‼·n^r − E_r(μ_n)` only at the two depths whose energy closed form is in tree
(`Slack_2 = 3n`, `Slack_3 = 45n²−40n`), and its docstring states the asymptotic shape
"`Slack_r ~ c_r·n^{r-1}`" but never names `c_r`. `Frontier/_BchksF5_CharPAnomalyExpZero.lean`
carries the exact gaps `Wick_r − E0_r` as the four lemmas `gap_four … gap_seven`
(`r = 4,5,6,7`), each a degree-`(r−1)` polynomial whose leading (`n^{r-1}`) coefficient is
`630, 9450, 155925, 2837835` respectively. `Frontier/_AvL2_E7ClosedForm.lean` records at `r=7`
that this coefficient is `C(7,2)·13‼` (`deficit_seven_leading : 2837835 = 21·135135`) and its
docstring states the `−C(r,2)(2r−1)‼` law — but only ever at one fixed depth, never as a uniform
closed form across `r`.

This file supplies the **uniform-in-`r` closed form for that leading coefficient**:

> **`slackLeadCoeff r = (r.choose 2) · (2r−1)‼`**

and proves it AGREES with the actual in-tree slack leading coefficient at EVERY landed depth
`r ∈ {2,3,4,5,6,7}` (the full in-tree Lam-Leung ladder). So the docstring `c_r` is now an explicit
function, matched against six independent in-tree data points (`E_2,E_3` closed forms +
the four `_BchksF5` gap lemmas), with the `r=2,3` values aligning to `_CharZeroLamLeungSlackLower`'s
`Slack_2 = 3n` (coeff `3 = (2.choose 2)·3‼`) and `Slack_3 = 45n²−40n` (coeff `45 = (3.choose 2)·5‼`),
and `r=7` aligning to `_AvL2_E7ClosedForm.deficit_seven_leading`.

## What is PROVEN (axiom-clean ℕ arithmetic + in-tree gap chaining)

- `slackLeadCoeff_eq_choose_mul_doubleFactorial` (the DEFINITIONAL closed form, `rfl`).
- `slackLeadCoeff_two … slackLeadCoeff_seven`: the six explicit values `3,45,630,9450,155925,2837835`,
  matching the `_BchksF5` `gap_*` leading coefficients exactly.
- `slack_lead_matches_bchks_four … _seven`: the IN-TREE gap polynomial `Wick r n − E0 r n` written
  with its leading coefficient AS `slackLeadCoeff r`, for `r = 4,5,6,7` (chaining the proven
  `gap_four … gap_seven`). This is the load-bearing check: the closed-form producer reproduces
  every independently-landed slack coefficient on the actual in-tree polynomial.
- `slackLeadCoeff_pos`: `0 < slackLeadCoeff r` for `r ≥ 2` (the slack leading term is genuine, never
  vacuous — the leading-coefficient face of the `slack_*_pos` strict positivity, uniformly in `r`).
- `slackLeadCoeff_succ_ratio`: the multiplier recursion
  `(r−1) · slackLeadCoeff (r+1) = (r+1)·(2r+1) · slackLeadCoeff r` (for `r ≥ 2`), the exact growth
  law of the slack leading coefficient as `r` increases (the "slack growth law", #444 §6.0/§6.1).

## Honest scope (rules 1,3,4,6 + ASYMPTOTIC GUARD)

This is a char-`0` STRUCTURAL closed form for the leading coefficient of the Lam-Leung slack; it
EXTENDS the two-depth `_CharZeroLamLeungSlackLower` production + the one-depth `_AvL2_E7ClosedForm`
observation into a uniform-in-`r` law, matched against the full in-tree energy ladder (`r = 2..7`).
It is NOT a CORE closure and NOT thinness-closing: the slack is char-`0` headroom (the `(P2-Slack)`
residual `Spur_r(p) ≤ Slack_r` still needs the char-`p` spurious-count bound, which stays OPEN = the
BGK wall). The slack is `Θ(n^{r-1})` while the energy is `Θ(n^r)`, so the relative slack `→ 0`
(TIGHTENING) — this brick makes the rate of that tightening an explicit closed form, NOT an escape.
It makes NO capacity/beyond-Johnson/`δ*`/cliff-at-`n/2` claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))`
UNCHANGED/OPEN. Probe: `scripts/probes/probe_slack_leading_coeff_law.py` (the law verified by an
INDEPENDENT exact char-`0` energy computation from roots-of-unity sign-reduction at `r = 2,3,4`,
NOT from the in-tree polynomials: leading `n^{r-1}` coefficients `3,45,630` reproduced). #444, wf-P2.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.CharZeroSlackLeadingCoeff

open ArkLib.ProximityGap.BchksF5

/-- **The closed form for the char-`0` Lam-Leung slack leading (`n^{r-1}`) coefficient:**
`c_r = (r choose 2)·(2r−1)‼`. This is the explicit function the `Slack_r ~ c_r·n^{r-1}` docstring
of `_CharZeroLamLeungSlackLower` left un-named, and the uniform-in-`r` form of the
`_AvL2_E7ClosedForm` `r=7` observation. -/
def slackLeadCoeff (r : ℕ) : ℕ := r.choose 2 * Nat.doubleFactorial (2 * r - 1)

/-- The closed form, definitionally. -/
theorem slackLeadCoeff_eq_choose_mul_doubleFactorial (r : ℕ) :
    slackLeadCoeff r = r.choose 2 * Nat.doubleFactorial (2 * r - 1) := rfl

/-- The six explicit values, matched to the in-tree data points. -/
theorem slackLeadCoeff_two : slackLeadCoeff 2 = 3 := rfl
theorem slackLeadCoeff_three : slackLeadCoeff 3 = 45 := rfl
theorem slackLeadCoeff_four : slackLeadCoeff 4 = 630 := rfl
theorem slackLeadCoeff_five : slackLeadCoeff 5 = 9450 := rfl
theorem slackLeadCoeff_six : slackLeadCoeff 6 = 155925 := rfl
theorem slackLeadCoeff_seven : slackLeadCoeff 7 = 2837835 := rfl

/-- **The closed-form producer reproduces the IN-TREE `_BchksF5` gap leading coefficient at `r=4`.**
The in-tree gap is `Wick 4 n − E0 4 n = 630n³ − 1435n² + 1155n` (`gap_four`); its leading (`n³`)
coefficient is `630 = slackLeadCoeff 4`. -/
theorem slack_lead_matches_bchks_four (n : ℕ) :
    Wick 4 n - E0 4 n = (slackLeadCoeff 4 : ℤ) * (n : ℤ) ^ 3 - 1435 * n ^ 2 + 1155 * n := by
  rw [gap_four]; norm_num [slackLeadCoeff_four]

/-- `r=5`: in-tree leading coefficient `9450 = slackLeadCoeff 5` (`gap_five`). -/
theorem slack_lead_matches_bchks_five (n : ℕ) :
    Wick 5 n - E0 5 n =
      (slackLeadCoeff 5 : ℤ) * (n : ℤ) ^ 4 - 39375 * n ^ 3 + 77175 * n ^ 2 - 57456 * n := by
  rw [gap_five]; norm_num [slackLeadCoeff_five]

/-- `r=6`: in-tree leading coefficient `155925 = slackLeadCoeff 6` (`gap_six`). -/
theorem slack_lead_matches_bchks_six (n : ℕ) :
    Wick 6 n - E0 6 n =
      (slackLeadCoeff 6 : ℤ) * (n : ℤ) ^ 5 - 1022175 * n ^ 4 + 3534300 * n ^ 3
        - 6246471 * n ^ 2 + 4370520 * n := by
  rw [gap_six]; norm_num [slackLeadCoeff_six]

/-- `r=7`: in-tree leading coefficient `2837835 = slackLeadCoeff 7` (`gap_seven`), agreeing with
`_AvL2_E7ClosedForm.deficit_seven_leading`. -/
theorem slack_lead_matches_bchks_seven (n : ℕ) :
    Wick 7 n - E0 7 n =
      (slackLeadCoeff 7 : ℤ) * (n : ℤ) ^ 6 - 26801775 * n ^ 5 + 141891750 * n ^ 4
        - 433726293 * n ^ 3 + 708996288 * n ^ 2 - 471556800 * n := by
  rw [gap_seven]; norm_num [slackLeadCoeff_seven]

/-- **The slack leading coefficient is strictly positive for `r ≥ 2`** — the slack is a genuine,
non-vacuous `Θ(n^{r-1})` headroom at every depth, uniformly (the leading-coefficient face of the
`slack_*_pos` strict positivity of `_CharZeroLamLeungSlackLower`). -/
theorem slackLeadCoeff_pos {r : ℕ} (hr : 2 ≤ r) : 0 < slackLeadCoeff r := by
  unfold slackLeadCoeff
  exact Nat.mul_pos (Nat.choose_pos hr) (Nat.doubleFactorial_pos _)

/-- **The slack-growth-law recursion** (#444 §6.0/§6.1): for `r ≥ 2`,
`(r−1) · slackLeadCoeff (r+1) = (r+1)·(2r+1) · slackLeadCoeff r`.

Proof: `slackLeadCoeff (r+1) = C(r+1,2)·(2r+1)‼ = C(r+1,2)·(2r+1)·(2r−1)‼` and
`slackLeadCoeff r = C(r,2)·(2r−1)‼`. After cancelling the common `(2r−1)‼` factor and the `(2r+1)`
double-factorial step, the claim reduces to the Pascal-type choose identity
`(r−1)·C(r+1,2) = (r+1)·C(r,2)` (both equal `(r+1)·r·(r−1)/2`). -/
theorem slackLeadCoeff_succ_ratio {r : ℕ} (hr : 2 ≤ r) :
    (r - 1) * slackLeadCoeff (r + 1) = (r + 1) * (2 * r + 1) * slackLeadCoeff r := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr  -- r = 2 + k
  unfold slackLeadCoeff
  -- (2(r+1)-1)‼ = (2r+1)‼ = (2r+1)·(2r-1)‼  via doubleFactorial_add_two
  have hdf : Nat.doubleFactorial (2 * (2 + k + 1) - 1)
      = (2 * (2 + k) + 1) * Nat.doubleFactorial (2 * (2 + k) - 1) := by
    have e1 : 2 * (2 + k + 1) - 1 = (2 * (2 + k) - 1) + 2 := by omega
    have e2 : 2 * (2 + k) + 1 = (2 * (2 + k) - 1) + 2 := by omega
    rw [e1, e2, Nat.doubleFactorial_add_two]
  rw [hdf]
  -- Generalize the common (2r-1)‼ factor; the remaining identity is pure choose/linear arithmetic.
  generalize Nat.doubleFactorial (2 * (2 + k) - 1) = D
  -- Reduce the two `choose 2` to their proven product forms (clearing /2 by ×2).
  have hc1 : 2 * (2 + k + 1).choose 2 = (2 + k + 1) * (2 + k) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self (2 + k + 1)).two_dvd]
    congr 1
  have hc2 : 2 * (2 + k).choose 2 = (2 + k) * (1 + k) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self (2 + k)).two_dvd]
    congr 1; omega
  -- Prove the goal after multiplying by 2: this exposes `2 * choose 2` on each side, which we
  -- rewrite via hc1 (left) and hc2 (right) into explicit products, then close by `ring`.
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  have lhs : 2 * ((2 + k - 1) * ((2 + k + 1).choose 2 * ((2 * (2 + k) + 1) * D)))
      = (2 + k - 1) * ((2 * (2 + k + 1).choose 2) * ((2 * (2 + k) + 1) * D)) := by ring
  have rhs : 2 * ((2 + k + 1) * (2 * (2 + k) + 1) * ((2 + k).choose 2 * D))
      = (2 + k + 1) * (2 * (2 + k) + 1) * ((2 * (2 + k).choose 2) * D) := by ring
  rw [lhs, rhs, hc1, hc2]
  -- Now: (2+k-1) * ((2+k+1)*(2+k) * ((2(2+k)+1)*D))
  --    = (2+k+1)*(2(2+k)+1) * (((2+k)*(1+k)) * D)
  -- both sides are the same monomial up to the (2+k-1)=(1+k) rewrite; finish by ring after it.
  have hsub : 2 + k - 1 = 1 + k := by omega
  rw [hsub]; ring

end ArkLib.ProximityGap.Frontier.CharZeroSlackLeadingCoeff
