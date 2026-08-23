/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CharZeroStepLawSlack
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E7ClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL2_E8ClosedForm

/-!
# Char-0 step-law discharge at the deep rungs `r = 6, 7` (#444, lane stepslack — high)

Companion to `CharZeroStepLawSlack` (which discharged the per-step Gaussian step-law
`E_{r+1} ≤ (2r+1)·n·E_r` char-0 for `r = 1..5`). This file extends the discharge to the two deepest
landed energy rungs using the in-tree `E_7` (`_AvL2_E7ClosedForm`) and `E_8` (`_AvL2_E8ClosedForm`),
so the char-0 step-law now holds across the **entire in-tree energy ladder `r = 1..7`** — every depth
at which an exact `E_r` closed form exists.

* `stepSlackHigh r n := (2r+1)·n·E_r − E_{r+1}` (r ∈ {6,7}; `E_6` from `CharZeroEnergy`, `E_7/E_8`
  from `E7ClosedForm`/`E8ClosedForm`).
* `step_slack_{six,seven}` — the EXACT `=` closed form of `S_r(n)`.
* `step_law_six` — `E_7 ≤ 13·n·E_6` (the (STEP) instance), char-0, `n ≥ 2`.
* `step_law_seven` — `E_8 ≤ 15·n·E_7` (the (STEP) instance), char-0, **`n ≥ 4`**. (Honest edge: the r=7
  step-slack `S_7` is NEGATIVE at the off-regime `n = 3` — a real root of the slack septic sits at
  `n ≈ 3.786` — so the step FAILS at `n = 3`; it holds at `n = 2` and for all `n ≥ 4`. Since `μ_n`
  has `n = 2^a`, the prize regime `n ≥ 16` is comfortably inside the valid band. The n=3 failure is
  documented, not swept under: it is exactly why a uniform-in-`n` step bound needs `n` a 2-power.)
* `step_slack_{six,seven}_lead` — leading coeff of `S_r` = `r·(2(r+1)−1)‼` (the uniform law, now r=6,7).

Honest scope: char-0 half only; the char-p step at `r ≈ ln q` (= the BGK/Burgess wall, §6.1) is
UNMOVED. This completes the *producer's* char-0 discharge across the full landed ladder; the
residual is exactly the char-p excess `W_r ≤ S_r`. Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option linter.style.longLine false

namespace ProximityGap.Frontier.CharZeroEnergy

open ProximityGap.Frontier.E7ClosedForm (E7)
open ProximityGap.Frontier.E8ClosedForm (E8)

/-- The exact char-0 Gaussian step-slack at the deep rungs `r ∈ {6,7}`:
`S_r(n) = (2r+1)·n·E_r − E_{r+1}`, off the in-tree `E_6, E_7, E_8` closed forms. -/
def stepSlackHigh : ℕ → ℤ → ℤ
  | 6, n => (2 * 6 + 1) * n * E6 n - E7 n
  | 7, n => (2 * 7 + 1) * n * E7 n - E8 n
  | _, _ => 0

/-! ## Exact step-slack closed forms (`=`) -/

theorem step_slack_six (n : ℤ) :
    stepSlackHigh 6 n =
      810810 * n ^ 6 - 13513500 * n ^ 5 + 95945850 * n ^ 4 - 352522170 * n ^ 3
        + 652179528 * n ^ 2 - 471556800 * n := by
  simp only [stepSlackHigh, E6, E7]; ring

theorem step_slack_seven (n : ℤ) :
    stepSlackHigh 7 n =
      14189175 * n ^ 7 - 326351025 * n ^ 6 + 3310807500 * n ^ 5 - 18549981450 * n ^ 4
        + 59300030790 * n ^ 3 - 100365259995 * n ^ 2 + 68492499075 * n := by
  simp only [stepSlackHigh, E7, E8]; ring

/-! ## Leading-coefficient law `lead(S_r) = r·(2(r+1)−1)‼` at r = 6, 7 -/

theorem step_slack_six_lead : (810810 : ℤ) = 6 * (Nat.doubleFactorial (2 * (6 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

theorem step_slack_seven_lead :
    (14189175 : ℤ) = 7 * (Nat.doubleFactorial (2 * (7 + 1) - 1) : ℤ) := by
  simp [Nat.doubleFactorial]

/-! ## The char-0 step-law `(STEP)` at the deep rungs: `E_{r+1} ≤ (2r+1)·n·E_r`

Both step-slack sextics/septics have one real factor-root just above `n = 2` (so the slack dips then
recovers); positive at integer `n ≥ 2`. Proved by the `n = 2` (`norm_num`) / `n ≥ 3` (shift `n = m+3`,
all shifted coefficients nonnegative) split, matching `step_law_five`. -/

theorem step_law_six (n : ℤ) (hn : 2 ≤ n) : E7 n ≤ 13 * n * E6 n := by
  have h : stepSlackHigh 6 n =
      810810 * n ^ 6 - 13513500 * n ^ 5 + 95945850 * n ^ 4 - 352522170 * n ^ 3
        + 652179528 * n ^ 2 - 471556800 * n := step_slack_six n
  simp only [stepSlackHigh] at h
  have hpos : (0:ℤ) ≤ 810810 * n ^ 5 - 13513500 * n ^ 4 + 95945850 * n ^ 3 - 352522170 * n ^ 2
      + 652179528 * n - 471556800 := by
    -- single real root ≈ 1.9996 < 2, so positive for all n ≥ 2; split n=2, n=3, n≥4 (shift m+4 ≥ 0).
    rcases eq_or_lt_of_le hn with h2 | h3
    · subst h2; norm_num
    · rcases eq_or_lt_of_le (show (3:ℤ) ≤ n by omega) with h3' | h4
      · rw [← h3']; norm_num
      · have hm0 : (0:ℤ) ≤ n - 4 := by linarith
        nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0) hm0,
          mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0,
          mul_nonneg (mul_nonneg hm0 hm0) hm0, mul_nonneg hm0 hm0, hm0]
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n) hpos]

theorem step_law_seven (n : ℤ) (hn : 4 ≤ n) : E8 n ≤ 15 * n * E7 n := by
  have h : stepSlackHigh 7 n =
      14189175 * n ^ 7 - 326351025 * n ^ 6 + 3310807500 * n ^ 5 - 18549981450 * n ^ 4
        + 59300030790 * n ^ 3 - 100365259995 * n ^ 2 + 68492499075 * n := step_slack_seven n
  simp only [stepSlackHigh] at h
  -- the slack septic factor has real roots ≈ 2.00 and ≈ 3.786, so it is positive for n ≥ 4
  -- (shift n = m + 4, m ≥ 0: all shifted coefficients are nonnegative).
  have hpos : (0:ℤ) ≤ 14189175 * n ^ 6 - 326351025 * n ^ 5 + 3310807500 * n ^ 4 - 18549981450 * n ^ 3
      + 59300030790 * n ^ 2 - 100365259995 * n + 68492499075 := by
    have hm0 : (0:ℤ) ≤ n - 4 := by linarith
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0) hm0) hm0,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0) hm0,
      mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0,
      mul_nonneg (mul_nonneg hm0 hm0) hm0, mul_nonneg hm0 hm0, hm0]
  nlinarith [h, mul_nonneg (by linarith : (0:ℤ) ≤ n) hpos]

/-! ## Strict positivity of the deep step-slack (`n ≥ 3`) -/

theorem step_slack_six_pos (n : ℤ) (hn : 3 ≤ n) : 0 < stepSlackHigh 6 n := by
  rw [step_slack_six]
  have hm0 : (0:ℤ) ≤ n - 3 := by linarith
  nlinarith [mul_pos (by linarith : (0:ℤ) < n)
    (by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0) hm0,
        mul_nonneg (mul_nonneg (mul_nonneg hm0 hm0) hm0) hm0,
        mul_nonneg (mul_nonneg hm0 hm0) hm0, mul_nonneg hm0 hm0, hm0] :
      (0:ℤ) < 810810 * n ^ 5 - 13513500 * n ^ 4 + 95945850 * n ^ 3 - 352522170 * n ^ 2
        + 652179528 * n - 471556800)]

end ProximityGap.Frontier.CharZeroEnergy

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_law_six
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_law_seven
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_slack_seven
#print axioms ProximityGap.Frontier.CharZeroEnergy.step_slack_six_pos
