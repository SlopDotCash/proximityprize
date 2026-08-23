/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SecondMomentExact

/-!
# The `M ≥ √n` sup-norm lower bound (#407)

The DC-subtracted second moment `∑_{b≠0}‖η_b‖² = q·|G| − |G|²` (`SecondMomentExact.sum_nonzero_sq`) is
spread over `q−1` non-trivial frequencies, so some non-trivial frequency attains at least the average:

> **`exists_nonzero_frequency_ge`** — `∃ b ≠ 0` with `‖η_b‖² ≥ (q·|G| − |G|²)/(q−1)`.

For `q > |G|` the right side is `≈ |G|`, so `M = max_{b≠0}‖η_b‖ ≥ √(|G|)·(1−o(1))`. Combined with the
conditional upper bound `M ≤ √(2|G|·ln q)` (`GaussPeriodOptimizedBound`), this **brackets the prize
sup-norm**: `√n · (1−o(1)) ≤ M ≤ √(2n ln q)`. The lower bound is unconditional and elementary
(Parseval / averaging); the upper bound is the open BGK content. The whole open question is the
`√(ln q)` gap between them.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SecondMomentExact

namespace ArkLib.ProximityGap.SecondMomentLowerBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Non-trivial sup-norm lower bound.** Some `b ≠ 0` has `‖η_b‖² ≥ (q·|G| − |G|²)/(q−1)` — the average
of the DC-subtracted second moment over the `q−1` non-trivial frequencies. Hence `M ≥ √n·(1−o(1))`. -/
theorem exists_nonzero_frequency_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hq : 1 < Fintype.card F) :
    ∃ b ∈ univ.erase (0 : F),
      ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1)
        ≤ ‖eta ψ G b‖ ^ 2 := by
  have hsum := sum_nonzero_sq hψ G
  set s : Finset F := univ.erase (0 : F) with hs
  have hscard : (s.card : ℝ) = (Fintype.card F : ℝ) - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    push_cast [Nat.cast_pred (by omega : 0 < Fintype.card F)]; ring
  have hsne : s.Nonempty := by
    rw [hs, ← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  have hq1ne : (Fintype.card F : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card F := by exact_mod_cast hq
    linarith
  by_contra h
  push_neg at h
  have hlt : ∑ b ∈ s, ‖eta ψ G b‖ ^ 2
      < ∑ _b ∈ s, ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1) :=
    Finset.sum_lt_sum_of_nonempty hsne h
  rw [Finset.sum_const, nsmul_eq_mul, hscard, hsum, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hq1ne] at hlt
  exact lt_irrefl _ hlt

end ArkLib.ProximityGap.SecondMomentLowerBound

#print axioms ArkLib.ProximityGap.SecondMomentLowerBound.exists_nonzero_frequency_ge
