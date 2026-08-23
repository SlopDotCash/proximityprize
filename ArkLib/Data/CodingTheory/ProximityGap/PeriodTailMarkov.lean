/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The moment ⟹ tail bridge for the Gauss-period histogram (#407)

The prize sup-norm `M = max_{b≠0}‖η_b‖` is governed by the TAIL of the period histogram
`{|η_b|² : b ≠ 0}`. Markov's inequality at order `r` turns the `2r`-th moment into a tail count:

> **`card_filter_mul_le_sum_pow`** — for `a : ι → ℝ` with `0 ≤ a` and `T > 0`,
> `#{b : T < a b}·T^r ≤ ∑_b (a b)^r`.

Instantiated with `a_b = |η_b|²` over `b ≠ 0` and `∑_b |η_b|^{2r} = q·A_r`, this is the bridge
`#{b≠0 : |η_b|² > T} ≤ q·A_r / T^r`. Optimizing over `r` (with the energy bound `A_r ≤ (2r−1)‼·n^r`)
gives the **sub-exponential tail** `#{b : |η_b|² > t·n} ≤ q·e^{−ct}` (conjecture C2), whence
`M ≤ √(c⁻¹·n·ln q)` by the union bound. This file machine-checks the elementary Markov step; the open
content is the energy bound `A_r ≤ Wick` (= BGK).

Issue #407.
-/

open Finset

namespace ArkLib.ProximityGap.PeriodTailMarkov

variable {ι : Type*} [Fintype ι]

/-- **Markov tail bound (finite, `r`-th moment).** For `a : ι → ℝ` nonnegative and `0 < T`, the number
of indices with `a b > T` times `T^r` is at most the `r`-th power-sum: `#{b : T < a b}·T^r ≤ ∑_b (a b)^r`.
This is the discrete Markov/Chebyshev inequality at order `r` — the moment ⟹ tail bridge. -/
theorem card_filter_mul_le_sum_pow (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ) :
    ((univ.filter (fun b => T < a b)).card : ℝ) * T ^ r ≤ ∑ b, (a b) ^ r := by
  set s := univ.filter (fun b => T < a b) with hs
  calc ((s.card : ℝ)) * T ^ r
      = ∑ _b ∈ s, T ^ r := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ b ∈ s, (a b) ^ r := by
        refine Finset.sum_le_sum (fun b hb => ?_)
        have hbT : T < a b := (Finset.mem_filter.mp hb).2
        exact pow_le_pow_left₀ hT.le hbT.le r
    _ ≤ ∑ b, (a b) ^ r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
          (fun i _ _ => pow_nonneg (ha i) r)

end ArkLib.ProximityGap.PeriodTailMarkov

#print axioms ArkLib.ProximityGap.PeriodTailMarkov.card_filter_mul_le_sum_pow
