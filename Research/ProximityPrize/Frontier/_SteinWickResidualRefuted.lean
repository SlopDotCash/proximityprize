/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Research.ProximityPrize.Frontier._ArxSteinWraparoundNoGo

/-!
# `SteinWickResidual` is false as stated

`SteinWickResidual C` quantifies over every `Nr n r p : ℕ` with `1 ≤ r` and `p ≠ 0`, and
asserts `dcCount Nr n r p ≤ C * wickBudget n r`. The collision count `Nr` is a free natural
number: nothing ties it to the actual depth-`r` collision count of `μ_n` modulo `p`, and
`dcCount Nr n r p = Nr - n^(2r)/p` is unbounded in `Nr` for fixed `n r p`.

So for every real `C` it fails already at `n = 1`, `r = 1`, `p = 1`: there `wickBudget 1 1 = 1`
and `dcCount Nr 1 1 1 = Nr - 1`, so any `Nr > C + 1` is a counterexample.

This refutes the recorded formal statement only. The intended statement, which would bound
`dcCount` for the genuine collision count of `μ_n` at depth `r ≈ log p`, is not touched, and
the Wick/BGK wall it names remains open. It does not close #164.
-/

set_option autoImplicit false

namespace ProximityGap.Frontier.ARX1.SteinWickResidualRefuted

open ProximityGap.Frontier.ARX1

/-- For every real `C`, the count `Nr = ⌈C⌉₊ + 2` at `n = r = p = 1` exceeds the Wick cap. -/
theorem not_steinWickResidual (C : ℝ) : ¬ SteinWickResidual C := by
  intro h
  have h1 := h (⌈C⌉₊ + 2) 1 1 1 le_rfl (by norm_num)
  have hC : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have hw : wickBudget 1 1 = 1 := by
    simp [wickBudget, Nat.doubleFactorial]
  rw [hw] at h1
  simp only [dcCount, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, one_pow, div_one,
    mul_one] at h1
  linarith

end ProximityGap.Frontier.ARX1.SteinWickResidualRefuted

#print axioms ProximityGap.Frontier.ARX1.SteinWickResidualRefuted.not_steinWickResidual
