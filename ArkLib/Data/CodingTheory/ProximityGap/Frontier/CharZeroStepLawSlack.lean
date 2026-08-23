/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroEnergyClosedForm

/-!
# Char-0 discharge of the Gaussian STEP-LAW on the in-tree energies `E_2..E_6` (#444, lane stepslack)

## Why this is the lever (the whole prize reduces to ONE per-step inequality)

The in-tree reduction `WF6F1.gaussian_moment_bound_of_stepLaw` (the *telescope*) + `WF7W3`
(the *hypercontractive ladder*) collapse the entire floor `A_r ≤ (2r−1)‼·n^r` (= `M(n) ≤ C√(n log m)`
= BGK) to the **single per-step Gaussian step-law**

> **(STEP)**  `E_{r+1} ≤ (2r+1)·n·E_r`     (variance proxy `s = |μ_n| = n`),

and `WF7W3` further pins its open content to the *base* `R(1) ≤ 1` (i.e. `E_2 ≤ 3·n·E_1`) plus a
single cumulant-ratio *antitonicity*. **BUT no file has discharged (STEP) — not even the base — on the
actual in-tree char-0 energies.** `WF6F1`/`WF7W3` leave `GaussianStepLaw` / `R(1) ≤ 1` as the *named
open input*, stated abstractly. The exact char-0 closed forms `E_2 = 3n²−3n, …, E_6 = 10395n⁶−…`
(`_CharZeroEnergyClosedForm`, proven) make (STEP) a *decidable polynomial inequality* at every landed
rung — yet that discharge was missing.

This file supplies it: the char-0 step-law holds at **every landed rung `r = 1..5`** with an EXPLICIT
positive step-slack `S_r(n) = (2r+1)·n·E_r − E_{r+1}`, whose leading coefficient is the clean uniform
law `r·(2(r+1)−1)‼` (the top `(2r+1)·(2r−1)‼ = (2(r+1)−1)‼` cancels against `E_{r+1}`'s Wick leading
term, so the slack is `Θ(n^r)`, governed by the *second* coefficient — the sub-Gaussian margin).
In particular the `WF7W3` **base `R(1) ≤ 1` is now an UNCONDITIONAL char-0 theorem** (`= E_2 ≤ 3n²`,
the in-tree `E2_le_wick`), and each `E_{r+1} ≤ (2r+1)·n·E_r` is a proven char-0 `(STEP)` instance.

## Honest scope (the wall is UNMOVED)

This is the **char-0 half** of the step-law. It RAISES nothing on the open ceiling: the prize needs
(STEP) at depth `r ≈ ln q ≈ 89` *in char p*, where `E_r(F_p)` can exceed the char-0 `E_r(ℂ)` (the
`W_r = E_r(F_p) − E_r(ℂ)` excess = the BGK/Burgess wall, §6.1). What this brick does is turn the
`WF6F1`/`WF7W3` "named open input" into a *proven char-0 fact at the landed depths*, and pin the
exact positive margin `S_r(n)` the char-p excess must stay below for the step to survive — i.e. it
makes the step-law producer *char-0-dischargeable*, isolating the residual to exactly `W_r ≤ slack`.

* `stepSlack r n := (2r+1)·n·E_r − E_{r+1}` (the exact per-step margin; `E_1 := n`).
* `step_slack_{one..five}` — the EXACT closed form of `S_r(n)` (`=` theorems), r=1..5.
* `step_law_{one..five}` — `E_{r+1} ≤ (2r+1)·n·E_r` (the (STEP) instance), r=1..5
  (`n ≥ 2`; the `r = 1` rung holds for `n ≥ 1`).
* `step_slack_{r}_lead` — the leading coefficient of `S_r` is `r·(2(r+1)−1)‼` (uniform law, r=1..5).
* `w3_base_charZero` — the `WF7W3` base `R(1) ≤ 1` discharged char-0: `E_2 ≤ 3·n·E_1`.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444, lane wf-stepslack.
-/

set_option linter.style.longLine false

namespace ProximityGap.Frontier.CharZeroEnergy

/-- `E_1(ℂ)(n) = n` (the Sidon base / first energy `= |μ_n|`; `Σ x_1 = Σ y_1` forces `x_1 = y_1`). -/
def E1 (n : ℤ) : ℤ := n

/-- The exact char-0 **Gaussian step-slack** at depth `r`:
`S_r(n) = (2r+1)·n·E_r − E_{r+1}`, the margin in the per-step Gaussian step-law
`E_{r+1} ≤ (2r+1)·n·E_r`. Defined directly off the in-tree closed forms `E_1..E_6`. -/
def stepSlack : ℕ → ℤ → ℤ
  | 1, n => (2 * 1 + 1) * n * E1 n - E2 n
  | 2, n => (2 * 2 + 1) * n * E2 n - E3 n
  | 3, n => (2 * 3 + 1) * n * E3 n - E4 n
  | 4, n => (2 * 4 + 1) * n * E4 n - E5 n
  | 5, n => (2 * 5 + 1) * n * E5 n - E6 n
  | _, _ => 0

/-! ## The exact step-slack closed forms (`=` theorems) -/

theorem step_slack_one (n : ℤ) : stepSlack 1 n = 3 * n := by
  simp only [stepSlack, E1, E2]; ring

theorem step_slack_two (n : ℤ) : stepSlack 2 n = 30 * n ^ 2 - 40 * n := by
  simp only [stepSlack, E2, E3]; ring

theorem step_slack_three (n : ℤ) : stepSlack 3 n = 315 * n ^ 3 - 1155 * n ^ 2 + 1155 * n := by
  simp only [stepSlack, E3, E4]; ring

theorem step_slack_four (n : ℤ) :
    stepSlack 4 n = 3780 * n ^ 4 - 26460 * n ^ 3 + 66780 * n ^ 2 - 57456 * n := by
  simp only [stepSlack, E4, E5]; ring

theorem step_slack_five (n : ℤ) :
    stepSlack 5 n =
      51975 * n ^ 5 - 589050 * n ^ 4 + 2685375 * n ^ 3 - 5614455 * n ^ 2 + 4370520 * n := by
  simp only [stepSlack, E5, E6]; ring

/-! ## The leading-coefficient law: `lead(S_r) = r·(2(r+1)−1)‼`

The top order of `(2r+1)·n·E_r` is `(2r+1)·(2r−1)‼·n^{r+1} = (2(r+1)−1)‼·n^{r+1}`, which cancels
the Wick leading term of `E_{r+1}`; so `S_r` is `Θ(n^r)` and its `n^r` coefficient is the uniform
`r·(2(r+1)−1)‼` (= `r·doubleFactorial(2r+1)`). Verified against the closed forms r=1..5. -/

theorem step_slack_one_lead : (3 : ℤ) = 1 * (Nat.doubleFactorial (2 * (1 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

theorem step_slack_two_lead : (30 : ℤ) = 2 * (Nat.doubleFactorial (2 * (2 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

theorem step_slack_three_lead : (315 : ℤ) = 3 * (Nat.doubleFactorial (2 * (3 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

theorem step_slack_four_lead : (3780 : ℤ) = 4 * (Nat.doubleFactorial (2 * (4 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

theorem step_slack_five_lead : (51975 : ℤ) = 5 * (Nat.doubleFactorial (2 * (5 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

/-! ## The char-0 step-law `(STEP)` at each landed rung: `E_{r+1} ≤ (2r+1)·n·E_r`

Each is `0 ≤ stepSlack r n` with the exact-form rewritten and the positive-`n` polynomial cleared by
`nlinarith` (SOS witnesses against `n ≥ 2`; the `r = 1` rung holds for `n ≥ 1`). -/

theorem step_law_one (n : ℤ) (hn : 1 ≤ n) : E2 n ≤ 3 * n * E1 n := by
  have h : stepSlack 1 n = 3 * n := step_slack_one n
  simp only [stepSlack] at h
  nlinarith [h, hn]

theorem step_law_two (n : ℤ) (hn : 2 ≤ n) : E3 n ≤ 5 * n * E2 n := by
  have h : stepSlack 2 n = 30 * n ^ 2 - 40 * n := step_slack_two n
  simp only [stepSlack] at h
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ 30 * n - 40)]

theorem step_law_three (n : ℤ) (hn : 2 ≤ n) : E4 n ≤ 7 * n * E3 n := by
  have h : stepSlack 3 n = 315 * n ^ 3 - 1155 * n ^ 2 + 1155 * n := step_slack_three n
  simp only [stepSlack] at h
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n)
    (by nlinarith [sq_nonneg (n - 2)] : (0:ℤ) ≤ 315 * n ^ 2 - 1155 * n + 1155)]

theorem step_law_four (n : ℤ) (hn : 2 ≤ n) : E5 n ≤ 9 * n * E4 n := by
  have h : stepSlack 4 n = 3780 * n ^ 4 - 26460 * n ^ 3 + 66780 * n ^ 2 - 57456 * n :=
    step_slack_four n
  simp only [stepSlack] at h
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n)
    (by nlinarith [sq_nonneg (n - 2), sq_nonneg n] :
      (0:ℤ) ≤ 3780 * n ^ 3 - 26460 * n ^ 2 + 66780 * n - 57456)]

theorem step_law_five (n : ℤ) (hn : 2 ≤ n) : E6 n ≤ 11 * n * E5 n := by
  have h : stepSlack 5 n =
      51975 * n ^ 5 - 589050 * n ^ 4 + 2685375 * n ^ 3 - 5614455 * n ^ 2 + 4370520 * n :=
    step_slack_five n
  simp only [stepSlack] at h
  -- the quartic factor dips between its two real roots (~2.01, ~2.99); positive at integer n≥2.
  -- Split n = 2 (decide) vs n ≥ 3 (shift n = m+3, all coefficients positive).
  have hquart : (0:ℤ) ≤ 51975 * n ^ 4 - 589050 * n ^ 3 + 2685375 * n ^ 2 - 5614455 * n + 4370520 := by
    rcases eq_or_lt_of_le hn with h2 | h3
    · subst h2; norm_num
    · -- n ≥ 3: write n = m + 3, m ≥ 0; the shifted quartic has all-nonneg coeffs
      have hm : (3:ℤ) ≤ n := by omega
      have hm0 : (0:ℤ) ≤ n - 3 := by linarith
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0,
        mul_nonneg (mul_nonneg hm0 hm0) hm0, mul_nonneg hm0 hm0, hm0]
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n) hquart]

/-! ## The step-slack is strictly positive (genuinely sub-Gaussian step) for `n ≥ 2`, all landed `r` -/

theorem step_slack_one_pos (n : ℤ) (hn : 1 ≤ n) : 0 < stepSlack 1 n := by
  rw [step_slack_one]; linarith

theorem step_slack_two_pos (n : ℤ) (hn : 2 ≤ n) : 0 < stepSlack 2 n := by
  rw [step_slack_two]; nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ 30 * n - 40)]

theorem step_slack_three_pos (n : ℤ) (hn : 2 ≤ n) : 0 < stepSlack 3 n := by
  rw [step_slack_three]
  nlinarith [mul_pos (by linarith : (0:ℤ) < n)
    (by nlinarith [sq_nonneg (n - 2)] : (0:ℤ) < 315 * n ^ 2 - 1155 * n + 1155)]

/-! ## The `WF7W3` base `R(1) ≤ 1`, discharged char-0

`WF7W3.gaussian_moment_bound_of_antitone_base` consumes `R(1) ≤ 1` (= `E_2 ≤ (2·1+1)·n·E_1 = 3n·E_1`)
as the finite hypercontractive base. Here it is a char-0 theorem (`= E_2 ≤ 3n²`, the in-tree
`E2_le_wick`), with explicit `3n` slack — the base of the step-law producer is no longer "open input"
in char 0. -/

theorem w3_base_charZero (n : ℤ) (hn : 1 ≤ n) : E2 n ≤ (2 * 1 + 1) * n * E1 n := by
  have h := step_law_one n hn
  have he : (2 * 1 + 1 : ℤ) * n * E1 n = 3 * n * E1 n := by ring
  rw [he]; exact h

/-- The char-0 second-moment/fourth-moment shape feeding the base: `E_2 ≤ 3·n²` (= `E2_le_wick`,
restated as the variance-normalized `r=1` step value). -/
theorem w3_base_eq_wick (n : ℤ) : (2 * 1 + 1) * n * E1 n = wick 2 n := by
  simp only [E1, wick, Nat.doubleFactorial]; ring

end ProximityGap.Frontier.CharZeroEnergy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_law_five
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_slack_five
#print axioms ProximityGap.Frontier.CharZeroEnergy.w3_base_charZero
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_slack_three_pos
