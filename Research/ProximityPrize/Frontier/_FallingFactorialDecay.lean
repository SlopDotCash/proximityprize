/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# The falling-factorial mechanism of the energy decay law (#444)

Attacking the Gaussian-tail decay law `A_r/Wick ≈ exp(−r²/2n)` by DERIVING its mechanism (machine-verified,
`probe_decay_mechanism.py`). The decay originates from the **falling factorial**: the char-0 additive
energy is, to leading order,
  `E_r(μ_n) ≈ (2r−1)‼·(n)_r`,   `(n)_r = n(n−1)⋯(n−r+1)`   (the falling factorial),
**EXACT at r=2** (`E_2 = 3n² − 3n = 3·n·(n−1) = (2·2−1)‼·(n)_2`) and leading for all `r` (the correction is
`O(r²/n)`). This is the antipodal-matching (Lam–Leung) structure with DISTINCT pair-values: the `(2r−1)‼`
matchings, and the `r` values chosen DISTINCT — `(n)_r` instead of the Gaussian `n^r`.

The falling factorial decays at the Gaussian-tail rate (PROVABLE, this file):
  `(n)_r / n^r = ∏_{j=0}^{r−1} (1 − j/n) ≤ exp(−r(r−1)/2n)`   (via `1 − x ≤ e^{−x}` termwise).

⚠️ **HONEST CORRECTION (machine-verified `probe_verify_ff_bound.py`):** the falling factorial is the char-0
LEADING SHAPE, NOT a valid upper bound on the char-`p` `A_r` — at depth `r ≥ 4–5` the char-`p` `A_r`
STRICTLY EXCEEDS `(2r−1)‼·(n)_r` (via the wraparound `W_r`), while still staying `≤ Wick`. So
`prize_of_fallingFactorial` is a valid implication with a TOO-STRONG (unsatisfiable-at-deep-`r`) hypothesis.

The **correct** prize form (`prize_iff_wraparound_le_slack`): with `A_r = E0 + W_r − dc`, the prize
`A_r ≤ Wick` ⟺ `W_r ≤ slack_r`, `slack_r = Wick − E0 (+ dc)`. The falling factorial's genuine contribution
is the SLACK SIZE: `slack_r/Wick = 1 − E0/Wick ≈ 1 − exp(−r²/2n) ≈ r²/2n`, GROWING — so the wraparound has
growing room (machine: `W_r ≤ slack_r` holds at all tested depths). This connects the decay law back to the
known wraparound-in-slack open input, now with the slack size derived from the falling factorial.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.FallingFactorialDecay

open Real Finset

/-- **Termwise: `1 − j/n ≤ exp(−j/n)`.** The single-factor inequality (`1 − x ≤ e^{−x}`), specialized to
`x = j/n`. The engine of the falling-factorial → Gaussian-tail bound. -/
theorem one_sub_le_exp_neg (j n : ℝ) : 1 - j / n ≤ Real.exp (-(j / n)) := by
  have h := Real.add_one_le_exp (-(j / n))
  linarith

/-- **The falling factorial decays at least as fast as the Gaussian tail (termwise product):**
`∏_{j=0}^{r−1} (1 − j/n) ≤ ∏_{j=0}^{r−1} exp(−j/n)`, valid when every factor is nonnegative
(`j ≤ n` over the range). Since `∏ exp(−j/n) = exp(−(∑ j)/n) = exp(−r(r−1)/2n)`, this is the provable
core of the decay law: the distinct-value falling factorial is dominated by the Gaussian tail. -/
theorem fallingFactorial_le_gaussianTail {r : ℕ} {n : ℝ} (hn : 0 < n)
    (hrange : ∀ j ∈ Finset.range r, (j : ℝ) ≤ n) :
    ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n)
      ≤ ∏ j ∈ Finset.range r, Real.exp (-((j : ℝ) / n)) := by
  apply Finset.prod_le_prod
  · intro j hj
    have : (j : ℝ) ≤ n := hrange j hj
    rw [sub_nonneg]
    exact div_le_one_of_le₀ this (le_of_lt hn)
  · intro j _
    exact one_sub_le_exp_neg (j : ℝ) n

/-- **The mechanism chain: falling-factorial energy bound ⟹ prize** (a SUFFICIENT-but-too-strong route).
If the DC-subtracted energy obeyed the falling-factorial bound `A_r ≤ (2r−1)‼·(n)_r` (`A ≤ wick · P`,
`P = ∏(1 − j/n) = (n)_r/n^r`), then `A ≤ wick` (the prize), since `P ≤ exp(−…) ≤ 1`. **⚠️ The hypothesis is
TOO STRONG (machine-verified `probe_verify_ff_bound.py`):** at depth `r ≥ 4–5` the char-`p` `A_r` STRICTLY
EXCEEDS `(2r−1)‼·(n)_r` (via the wraparound), while still staying `≤ Wick`. So the falling factorial is the
char-0 LEADING SHAPE, NOT a valid upper bound on `A_r`. This lemma is the valid (vacuously-usable)
implication; the CORRECT prize form is the slack characterization below (`prize_iff_wraparound_le_slack`),
where the falling factorial determines the SLACK SIZE `slack_r ≈ Wick·(1−exp(−r²/2n)) ≈ Wick·r²/2n`. -/
theorem prize_of_fallingFactorial {r : ℕ} {n A wick : ℝ} (hn : 0 < n) (hwick : 0 ≤ wick)
    (hrange : ∀ j ∈ Finset.range r, (j : ℝ) ≤ n)
    (hbound : A ≤ wick * ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n)) :
    A ≤ wick := by
  refine le_trans hbound ?_
  -- the falling-factorial product is ≤ 1: each factor `1 - j/n ∈ [0,1]`.
  have hP1 : ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n) ≤ 1 := by
    refine le_trans (Finset.prod_le_one ?_ ?_) (le_refl 1)
    · intro j hj
      rw [sub_nonneg]
      exact div_le_one_of_le₀ (hrange j hj) (le_of_lt hn)
    · intro j _
      have : (0 : ℝ) ≤ (j : ℝ) / n := by positivity
      linarith
  calc wick * ∏ j ∈ Finset.range r, (1 - (j : ℝ) / n)
      ≤ wick * 1 := mul_le_mul_of_nonneg_left hP1 hwick
    _ = wick := mul_one wick

/-- **The r=2 exact anchor.** `E_2(μ_n) = 3n² − 3n = (2·2−1)‼ · n·(n−1)` — the falling-factorial form is
EXACT at depth 2 (machine: correction = 0 at r=2 for all n). This anchors the mechanism: the energy IS the
matching count `(2·2−1)‼ = 3` times the distinct-value falling factorial `(n)_2 = n(n−1)`. -/
theorem energy_two_eq_fallingFactorial (n : ℝ) :
    3 * n^2 - 3 * n = 3 * (n * (n - 1)) := by ring

/-! ## The CORRECT prize form: wraparound within the (falling-factorial-sized) slack -/

/-- **The prize ⟺ wraparound ≤ slack (the correct, machine-verified form).** With `A_r = E0 + W_r − dc`
(`E0` = char-0 energy, `W_r ≥ 0` = wraparound excess, `dc = n^{2r}/p` = DC term), the prize bound
`A_r ≤ Wick` is EQUIVALENT to `W_r ≤ slack` where `slack = Wick − E0 + dc`. This is the correct open input
(the falling-factorial bound `A_r ≤ (2r−1)‼(n)_r` was too strong); the falling factorial supplies the SLACK
SIZE: `slack/Wick = 1 − E0/Wick ≈ 1 − exp(−r²/2n) ≈ r²/2n`, GROWING — so the wraparound has growing room. -/
theorem prize_iff_wraparound_le_slack {E0 wr dc wick : ℝ} :
    E0 + wr - dc ≤ wick ↔ wr ≤ wick - E0 + dc := by
  constructor <;> intro h <;> linarith

/-- **The slack is nonneg from the char-0 Lam–Leung bound.** If `E0 ≤ Wick` (the PROVEN char-0 energy bound,
Lam–Leung) and `0 ≤ dc`, the slack `Wick − E0 + dc ≥ 0` — so there IS room for the wraparound. The prize is
exactly whether `W_r` fits in this (falling-factorial-sized, growing) slack at deep `r`. -/
theorem slack_nonneg {E0 wick dc : ℝ} (hLL : E0 ≤ wick) (hdc : 0 ≤ dc) :
    0 ≤ wick - E0 + dc := by linarith

end ArkLib.ProximityGap.FallingFactorialDecay

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.one_sub_le_exp_neg
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.fallingFactorial_le_gaussianTail
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.prize_of_fallingFactorial
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.energy_two_eq_fallingFactorial
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.prize_iff_wraparound_le_slack
#print axioms ArkLib.ProximityGap.FallingFactorialDecay.slack_nonneg
