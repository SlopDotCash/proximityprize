/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Basic.Entropy

/-!
# Endpoint and capacity values of the q-ary entropy `qEntropy`

`Basic/Entropy.lean` defines `CodingTheory.qEntropy q x` and proves `qEntropy q 0 = 0`.
This file adds the two remaining closed-form values that the capacity-side list-decoding /
correlated-agreement arguments use (ABF26 §2–§4):

* `qEntropy_one`         — `H_q(1) = log_q (q-1)`;
* `qEntropy_capacity_eq_one` — `H_q((q-1)/q) = 1`, i.e. the q-ary entropy peaks at `1` on the
  "capacity" radius `1 - 1/q`.

Kept in a separate file from the hot `Basic/Entropy.lean` def site. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- The q-ary entropy at `x = 1` is `log_q (q-1)`. -/
theorem qEntropy_one (hq : 2 ≤ q) : qEntropy q 1 = Real.logb q ((q : ℝ) - 1) := by
  unfold qEntropy
  simp [Real.logb_one]

/-- **q-ary entropy peaks at `1` on the capacity point.** For `2 ≤ q`,
`H_q((q-1)/q) = 1` — the entropy maximum, attained at the capacity radius `1 - 1/q`. -/
theorem qEntropy_capacity_eq_one (hq : 2 ≤ q) :
    qEntropy q (((q : ℝ) - 1) / (q : ℝ)) = 1 := by
  have hb : (1 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hq0' : (q : ℝ) ≠ 0 := ne_of_gt hq0
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hself : Real.logb (q : ℝ) (q : ℝ) = 1 := Real.logb_self_eq_one hb
  have h1sub : (1 : ℝ) - ((q : ℝ) - 1) / (q : ℝ) = 1 / (q : ℝ) := by
    field_simp <;> ring
  unfold qEntropy
  rw [h1sub]
  rw [Real.logb_div (ne_of_gt hqm1) hq0', Real.logb_div one_ne_zero hq0', Real.logb_one,
    hself]
  field_simp
  ring

end CodingTheory
