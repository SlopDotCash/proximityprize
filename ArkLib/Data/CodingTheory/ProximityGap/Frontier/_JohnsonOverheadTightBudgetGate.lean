/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Johnson-range overhead vs the exact production budget

The in-tree `ProductionJohnsonBudget.lean` gives the positive field-slack statement: a
Johnson-range MCA bound of size

```text
  K * n / q,   K = 4(M+1)^5 + 2(M+1),
```

fits a target error once the field size is enlarged by the overhead factor `K`.

This file records the complementary tight-budget obstruction.  If the deployment target is exactly
the production ratio `n/q` (equivalently `q * epsilon = n` bad scalars), then a bound of the form
`K * n / q` proves the target only when `K <= 1`.  Thus Johnson/Hab25/BCHKS-style overheads cannot
by themselves certify the zero-loss prize budget at the same field size; either the field has to be
larger by the overhead factor, or one needs the genuinely above-Johnson/budget-sized incidence input.

This is pure scale bookkeeping.  It does not assert or refute any MCA theorem, and it does not touch
the BGK/Paley core.
-/

namespace ArkLib.ProximityGap.Frontier.JohnsonOverheadTightBudgetGate

/-- The coarse Johnson-range overhead appearing in `ProductionJohnsonBudget.lean`. -/
def johnsonOverhead (M : ℕ) : ℕ :=
  4 * (M + 1) ^ 5 + 2 * (M + 1)

/-- Exact production target ratio: `n/q`. -/
noncomputable def tightProductionBudget (n q : ℝ) : ℝ :=
  n / q

/-- A Johnson-range theorem with multiplicative overhead `K`: `K * n / q`. -/
noncomputable def overheadJohnsonBound (K n q : ℝ) : ℝ :=
  K * n / q

/-- **Tight-budget criterion.**  At a fixed field size `q`, a bound `K * n / q` fits the exact
production target `n / q` if and only if the overhead is at most one. -/
theorem overhead_bound_le_tightBudget_iff {K n q : ℝ} (hn : 0 < n) (hq : 0 < q) :
    overheadJohnsonBound K n q ≤ tightProductionBudget n q ↔ K ≤ 1 := by
  unfold overheadJohnsonBound tightProductionBudget
  constructor
  · intro h
    have hmul : (K * n / q) * q ≤ (n / q) * q :=
      mul_le_mul_of_nonneg_right h hq.le
    have hleft : (K * n / q) * q = K * n := by
      field_simp [ne_of_gt hq]
    have hright : (n / q) * q = n := by
      field_simp [ne_of_gt hq]
    have hcancel : K * n ≤ n := by
      simpa [hleft, hright] using hmul
    have hdiv : (K * n) / n ≤ n / n :=
      div_le_div_of_nonneg_right hcancel hn.le
    have hleft_cancel : (K * n) / n = K := by
      field_simp [ne_of_gt hn]
    have hright_cancel : n / n = 1 := by
      field_simp [ne_of_gt hn]
    simpa [hleft_cancel, hright_cancel] using hdiv
  · intro hK
    have hnonneg : 0 ≤ n / q := div_nonneg hn.le hq.le
    calc
      K * n / q = K * (n / q) := by ring
      _ ≤ 1 * (n / q) := mul_le_mul_of_nonneg_right hK hnonneg
      _ = n / q := by ring

/-- If the overhead is strictly larger than one, the same-field Johnson-range bound cannot certify
the exact production target. -/
theorem overhead_bound_misses_tightBudget_of_one_lt {K n q : ℝ}
    (hK : 1 < K) (hn : 0 < n) (hq : 0 < q) :
    ¬ overheadJohnsonBound K n q ≤ tightProductionBudget n q := by
  intro hfit
  have hle : K ≤ 1 := (overhead_bound_le_tightBudget_iff hn hq).mp hfit
  linarith

/-- Concrete production-budget guardrail for the commonly used cap `M = 64`: the overhead is
strictly bigger than one. -/
theorem johnsonOverhead64_gt_one : (1 : ℝ) < (johnsonOverhead 64 : ℝ) := by
  norm_num [johnsonOverhead]

/-- At exact target `n/q`, the `M = 64` Johnson-range overhead from
`ProductionJohnsonBudget.lean` cannot fit without extra field-size slack. -/
theorem johnsonOverhead64_misses_exactBudget {n q : ℝ} (hn : 0 < n) (hq : 0 < q) :
    ¬ overheadJohnsonBound (johnsonOverhead 64 : ℝ) n q ≤ tightProductionBudget n q :=
  overhead_bound_misses_tightBudget_of_one_lt johnsonOverhead64_gt_one hn hq

#print axioms overhead_bound_le_tightBudget_iff
#print axioms overhead_bound_misses_tightBudget_of_one_lt
#print axioms johnsonOverhead64_gt_one
#print axioms johnsonOverhead64_misses_exactBudget

end ArkLib.ProximityGap.Frontier.JohnsonOverheadTightBudgetGate
