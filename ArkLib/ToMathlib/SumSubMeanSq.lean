/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Variance as a raw-moment identity over a finite type

The computational variance identity: for `X : ι → ℝ` over a `Fintype` with `N = |ι|` and mean
`μ = (∑ X) / N`,

  `∑ i, (X i − μ)²  =  (∑ i, X i²)  −  (∑ i, X i)² / N`.

This expresses the sum of squared deviations (the numerator of Chebyshev's bound, `FinsetChebyshev`)
in terms of the raw first and second moments `∑ X` and `∑ X²`, so a concrete variance bound can be
computed directly from the moment bricks.

## Main result (`sorry`-free; axioms = `propext, Classical.choice, Quot.sound`)

* `sum_sub_mean_sq_eq`.
-/

namespace ArkLib

open Finset

/-- **Variance = raw-moment identity.** `∑ (X i − μ)² = ∑ X i² − (∑ X i)²/N` for `μ` the mean. -/
theorem sum_sub_mean_sq_eq {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → ℝ) :
    ∑ i, (X i - (∑ j, X j) / (Fintype.card ι : ℝ)) ^ 2
      = (∑ i, X i ^ 2) - (∑ i, X i) ^ 2 / (Fintype.card ι : ℝ) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_pos).ne'
  have hexp : ∀ i, (X i - (∑ j, X j) / (Fintype.card ι : ℝ)) ^ 2
      = X i ^ 2 - X i * (2 * ((∑ j, X j) / (Fintype.card ι : ℝ)))
        + ((∑ j, X j) / (Fintype.card ι : ℝ)) ^ 2 := by
    intro i; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring
#print axioms ArkLib.sum_sub_mean_sq_eq
