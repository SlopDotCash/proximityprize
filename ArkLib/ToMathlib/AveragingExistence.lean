/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Averaging / first-moment existence

From a lower bound on a finite sum of real values, extract an index whose value is at least
that bound divided by the number of terms. The values need not be nonnegative.

This is the constant-function specialization of `Finset.exists_le_of_sum_le`.
-/

namespace AveragingExistence

open Finset BigOperators

variable {ι : Type*}

/-- **First-moment existence (sum form).**  If `∑_{i ∈ s} f i ≥ c` and `s` is nonempty, some
`i ∈ s` has `f i ≥ c / #s`.  (The mean is at most the max.) -/
theorem exists_ge_sum_div_card
    (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ)
    (hsum : c ≤ ∑ i ∈ s, f i) :
    ∃ i ∈ s, c / s.card ≤ f i := by
  classical
  have hcard : (s.card : ℝ) ≠ 0 :=
    (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)).ne'
  apply Finset.exists_le_of_sum_le hs
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ c hcard] using hsum

end AveragingExistence
