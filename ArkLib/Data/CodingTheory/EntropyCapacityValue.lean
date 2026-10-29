/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.Basic.Entropy

/-!
# Endpoint and capacity values of the q-ary entropy `qEntropy`

`Basic/Entropy.lean` defines `CodingTheory.qEntropy q x` and proves `qEntropy q 0 = 0`.
The canonical library supplies the endpoint value. This file retains the capacity-value alias that the capacity-side list-decoding /
correlated-agreement arguments use (ABF26 §2–§4):

* `qEntropy_one` is supplied by the canonical module without an extra lower-bound premise;
* `qEntropy_capacity_eq_one` — `H_q((q-1)/q) = 1`, i.e. the q-ary entropy peaks at `1` on the
  "capacity" radius `1 - 1/q`.

Kept in a separate file from the hot `Basic/Entropy.lean` def site. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- **q-ary entropy peaks at `1` on the capacity point.** For `2 ≤ q`,
`H_q((q-1)/q) = 1` — the entropy maximum, attained at the capacity radius `1 - 1/q`. -/
theorem qEntropy_capacity_eq_one (hq : 2 ≤ q) :
    qEntropy q (((q : ℝ) - 1) / (q : ℝ)) = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [sub_div, div_self hq0]
  exact qEntropy_one_sub_inv hq

end CodingTheory
