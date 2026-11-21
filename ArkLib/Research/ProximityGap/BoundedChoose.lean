/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Data.Nat.Choose.Basic

/-! # Binomial coefficients capped at a supplied budget

The support-rank evaluator only needs comparisons with a budget. The recurrence
visits the increasing half of the binomial row and stops when it reaches the cap.
-/

namespace ProximityPrize.BoundedChoose

private def walk (n cap : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, value => min value cap
  | remaining + 1, i, value =>
    if cap ≤ value then cap else
      walk n cap remaining (i + 1) (value * (n - i) / (i + 1))

private theorem increasing {n i remaining : ℕ} (h : i + remaining ≤ n / 2) :
    n.choose i ≤ n.choose (i + remaining) := by
  induction remaining with
  | zero => simp
  | succ r ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem walk_eq (n cap remaining i : ℕ) (h : i + remaining ≤ n / 2) :
    walk n cap remaining i (n.choose i) = min (n.choose (i + remaining)) cap := by
  induction remaining generalizing i with
  | zero => simp [walk]
  | succ r ih =>
    rw [walk]
    split_ifs with stop
    · exact (Nat.min_eq_right (stop.trans (increasing h))).symm
    · rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (by omega : 0 < i + 1)]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (i + 1) (by omega)

/-- Compute the smaller of a binomial coefficient and a cap without materializing the full row. -/
def capped (n k cap : ℕ) : ℕ :=
  if n < k then 0 else walk n cap (min k (n - k)) 0 1

/-- The early exit preserves the truncated binomial coefficient for all natural inputs. -/
theorem capped_eq (n k cap : ℕ) : capped n k cap = min (n.choose k) cap := by
  unfold capped
  split_ifs with outside
  · simp [Nat.choose_eq_zero_of_lt outside]
  · have h : 0 + min k (n - k) ≤ n / 2 := by omega
    have w := walk_eq n cap (min k (n - k)) 0 h
    rw [Nat.choose_zero_right, Nat.zero_add] at w
    rw [w]
    rcases le_total k (n - k) with small | large
    · rw [min_eq_left small]
    · rw [min_eq_right large, Nat.choose_symm (by omega)]

end ProximityPrize.BoundedChoose
