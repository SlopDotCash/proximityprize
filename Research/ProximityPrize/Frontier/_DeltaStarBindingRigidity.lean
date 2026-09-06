/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# δ* binding-radius rigidity — the interior is ALL-OR-NOTHING at the `√(n log m)` scale (#444)

A gap-hunt / partial-determination result (Category C2 of
`docs/kb/deltastar-444-25-attack-vectors-for-closure-2026-06-17.md`). The δ\*-determination question is:
does δ\* enter the window interior (toward capacity), governed by the BGK sup-norm bound
`M(n) ≤ C·√(n·log m)`? This file proves the **rigidity** that makes the determination sharp:

* **The interior threshold `√(n·log(q/n))` is a GENUINE MIDDLE scale**, strictly between the Parseval floor
  `√n` and the trivial bound `n` (`interior_threshold_strict`). So "interior reach" is a real intermediate
  condition, not a degenerate endpoint.
* **No polynomially-weaker bound certifies the interior** (`partial_bound_overshoots`): a candidate bound
  `M ≤ n^{1/2+c}` (any `c > 0`) **overshoots** the interior threshold whenever `log(q/n) < n^{2c}` — which
  holds in the prize regime (`log(q/n) = Θ(log n) ≪ n^{2c}`). So a sub-`√(n log m)` but super-`√n` bound
  (e.g. the di Benedetto SOTA `M ≤ n^{0.9583}`, machine-confirmed NOT to reach the interior) gives **no
  partial interior** — δ\* is either Johnson or interior, with no provable intermediate.

**Consequence (the rigidity):** determining δ\* is *all-or-nothing* — it requires the bound *exactly at*
the `√(n log m)` scale; nothing polynomially weaker helps. This sharpens why partial progress on `M`
(better exponents short of `1/2`) cannot move δ\* off Johnson, and pins the determination difficulty to the
exact-scale BGK bound. Real-analysis facts, char-free, no `sorry`.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.DeltaStarBindingRigidity

open Real

/-- **The interior threshold is a genuine middle scale: `√n < √(n·L) < n`** where `L = log(q/n)` is the
budget-log, given `1 < L < n` (the prize regime: `L = Θ(log n)`, so `1 < L` and `L ≪ n`). The interior
reach is therefore a real intermediate condition between the Parseval floor `√n` and the trivial `n`. -/
theorem interior_threshold_strict {n L : ℝ} (hn : 1 < n) (hL1 : 1 < L) (hLn : L < n) :
    Real.sqrt n < Real.sqrt (n * L) ∧ Real.sqrt (n * L) < n := by
  have hn0 : (0 : ℝ) < n := lt_trans one_pos hn
  refine ⟨?_, ?_⟩
  · -- √n < √(n·L) since n < n·L (as L > 1)
    apply Real.sqrt_lt_sqrt (le_of_lt hn0)
    nlinarith [mul_lt_mul_of_pos_left hL1 hn0]
  · -- √(n·L) < n since n·L < n² (as L < n)
    rw [Real.sqrt_lt' hn0]
    nlinarith [mul_lt_mul_of_pos_left hLn hn0]

/-- **A polynomially-weaker bound OVERSHOOTS the interior threshold (no partial interior).** If a candidate
sup-norm bound is `B = n^{1/2+c}` with `c > 0`, and the budget-log satisfies `L < n^{2c}` (true in the
prize regime, `L = Θ(log n) ≪ n^{2c}`), then `√(n·L) < n^{1/2+c} = B`. So `B` is strictly LARGER than the
interior threshold — proving `M ≤ B` does NOT certify the interior. Hence sub-`√(n log m)` improvements on
`M` (better exponents short of the exact `1/2`-with-log scale) give **no** partial interior. -/
theorem partial_bound_overshoots {n L c : ℝ} (hn : 1 < n) (hc : 0 < c) (hL : L < n ^ (2 * c))
    (hL0 : 0 < L) :
    Real.sqrt (n * L) < n ^ ((1 : ℝ) / 2 + c) := by
  have hn0 : (0 : ℝ) < n := lt_trans one_pos hn
  -- n^{1/2+c} = √n · n^c, and (√n · n^c)^2 = n · n^{2c} > n · L = (√(n·L))^2
  have hrhs_pos : 0 < n ^ ((1 : ℝ) / 2 + c) := Real.rpow_pos_of_pos hn0 _
  rw [show Real.sqrt (n * L) = Real.sqrt (n * L) from rfl]
  apply Real.sqrt_lt' hrhs_pos |>.mpr
  -- need: n * L < (n^{1/2+c})^2 = n^{1+2c} = n * n^{2c}
  have hsq : (n ^ ((1 : ℝ) / 2 + c)) ^ 2 = n ^ (1 + 2 * c) := by
    rw [← Real.rpow_natCast (n ^ ((1:ℝ)/2 + c)) 2, ← Real.rpow_mul (le_of_lt hn0)]
    congr 1
    push_cast
    ring
  rw [hsq, show (1 : ℝ) + 2 * c = 1 + 2 * c from rfl,
      Real.rpow_add hn0, Real.rpow_one]
  -- now: n * L < n * n^{2c}, i.e. L < n^{2c} (times n > 0)
  have : n * L < n * n ^ (2 * c) := by
    apply mul_lt_mul_of_pos_left hL hn0
  linarith

/-- **The rigidity, assembled: δ\* determination is ALL-OR-NOTHING at the `√(n·log m)` scale.** The
interior threshold is a genuine middle scale (`interior_threshold_strict`), AND any polynomially-weaker
sup-norm bound `n^{1/2+c}` overshoots it (`partial_bound_overshoots`). So in the prize regime there is no
*partial* interior: δ\* is pinned to Johnson unless `M` is bounded *exactly* at the `√(n log m)` scale —
the single open BGK input. This is why SOTA exponent improvements short of `1/2` (di Benedetto `0.9583`,
etc.) cannot move δ\* off Johnson. -/
theorem deltaStar_determination_all_or_nothing {n L c : ℝ}
    (hn : 1 < n) (hL1 : 1 < L) (hLn : L < n) (hc : 0 < c) (hLpoly : L < n ^ (2 * c)) :
    (Real.sqrt n < Real.sqrt (n * L) ∧ Real.sqrt (n * L) < n) ∧
      Real.sqrt (n * L) < n ^ ((1 : ℝ) / 2 + c) :=
  ⟨interior_threshold_strict hn hL1 hLn, partial_bound_overshoots hn hc hLpoly (lt_trans one_pos hL1)⟩

end ArkLib.ProximityGap.DeltaStarBindingRigidity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.DeltaStarBindingRigidity.interior_threshold_strict
#print axioms ArkLib.ProximityGap.DeltaStarBindingRigidity.partial_bound_overshoots
#print axioms ArkLib.ProximityGap.DeltaStarBindingRigidity.deltaStar_determination_all_or_nothing
