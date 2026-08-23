/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import ArkLib.ToMathlib.SqSumCardSupport

/-!
# Second-moment counting bricks (GCXK25 / CS25)

Two reusable second-moment results for the correlated-agreement / list-decoding proximity work:

* `N_le_of_base` — the **GCXK25 second-moment algebra core** (issues #67/#75): from the base
  inequality `N·S² ≤ n·(S + (N-1)·B)` with a positive denominator `S² - n·B`, isolate
  `N ≤ n·(S - B)/(S² - n·B)`. Pure real algebra; the Cauchy–Schwarz combinatorics that produces the
  base inequality is supplied separately by the GCXK25 second-moment machinery.

* `card_support_ge_of_first_second_moment` — the **CS25 / Paley–Zygmund covered-fraction lower
  bound** (issues #22/#75): from a first-moment lower bound `M ≤ ∑ f` and a second-moment upper
  bound `∑ f² ≤ V`, the support is large: `M²/V ≤ |support f|`. Built on the in-tree
  `Finset.sq_sum_le_card_support_mul_sum_sq` (Cauchy–Schwarz / Chebyshev sum inequality).
-/

open Finset

/-- **GCXK25 second-moment algebra core.** From `N·S² ≤ n·(S + (N-1)·B)` and `0 < S² - n·B`,
`N ≤ n·(S - B)/(S² - n·B)`. -/
theorem N_le_of_base {N n S B : ℝ}
    (hbase : N * S ^ 2 ≤ n * (S + (N - 1) * B)) (hden : 0 < S ^ 2 - n * B) :
    N ≤ n * (S - B) / (S ^ 2 - n * B) := by
  rw [le_div_iff₀ hden]
  nlinarith [hbase]

/-- **CS25 / Paley–Zygmund covered-fraction lower bound.** If `M ≤ ∑ f` (first moment) and
`∑ f² ≤ V` (second moment) with `0 ≤ M` and `0 < V`, then `M²/V ≤ |support f|`. -/
theorem card_support_ge_of_first_second_moment {α : Type*} [Fintype α] (f : α → ℝ)
    {M V : ℝ} (hM : M ≤ ∑ a, f a) (hM0 : 0 ≤ M) (hV : (∑ a, f a ^ 2) ≤ V) (hV0 : 0 < V) :
    M ^ 2 / V ≤ ((univ.filter (fun a => f a ≠ 0)).card : ℝ) := by
  classical
  rw [div_le_iff₀ hV0]
  have hsum_nonneg : 0 ≤ ∑ a, f a := le_trans hM0 hM
  have h1 : M ^ 2 ≤ (∑ a, f a) ^ 2 := by nlinarith [hM, hM0, hsum_nonneg]
  have h2 : (∑ a, f a) ^ 2
      ≤ ((univ.filter (fun a => f a ≠ 0)).card : ℝ) * (∑ a, f a ^ 2) :=
    Finset.sq_sum_le_card_support_mul_sum_sq f
  have hcard_nonneg : (0 : ℝ) ≤ ((univ.filter (fun a => f a ≠ 0)).card : ℝ) := by positivity
  calc M ^ 2 ≤ (∑ a, f a) ^ 2 := h1
    _ ≤ ((univ.filter (fun a => f a ≠ 0)).card : ℝ) * (∑ a, f a ^ 2) := h2
    _ ≤ ((univ.filter (fun a => f a ≠ 0)).card : ℝ) * V :=
        mul_le_mul_of_nonneg_left hV hcard_nonneg

#print axioms N_le_of_base
#print axioms card_support_ge_of_first_second_moment
