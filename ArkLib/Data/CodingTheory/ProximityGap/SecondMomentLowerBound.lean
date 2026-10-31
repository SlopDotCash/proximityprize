/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SecondMomentExact

/-!
# The Parseval sup-norm lower bound `M² ≥ n(q−n)/(q−1)` (#407)

The DC-subtracted second moment `∑_{b≠0}‖η_b‖² = q·|G| − |G|²` (`SecondMomentExact.sum_nonzero_sq`) is
spread over `q−1` non-trivial frequencies, so some non-trivial frequency attains at least the average:

> **`exists_nonzero_frequency_ge`** — `∃ b ≠ 0` with `‖η_b‖² ≥ (q·|G| − |G|²)/(q−1)`.

With `n = |G|` and `M = max_{b≠0}‖η_b‖` this is exactly `M² ≥ n(q−n)/(q−1)`. For `n > 1` the right
side is strictly less than `n`, so it does **not** give `M ≥ √n`: e.g. over `F_3` with
`G = {1,2}` both nonzero periods are `−1`, so `M = 1 < √2` (and `G = F` gives `M = 0`). Only in the
sparse regime `n/q → 0` is this `M ≥ √n·(1−o(1))`; `q > n` alone does not give that.

Combined with the conditional upper bound `M² ≤ 2e·n·r` at any `r ≥ max(1, ln q)` (so
`M ≤ √(2e·n·⌈ln q⌉)`; `DCOptimized.eta_sq_le_dcOptimized` under `DCEnergyBound`, assembled in
`SupNormBracket`), this brackets the prize sup-norm. The sharp-constant form `√(2n ln q)` is only
an asymptotic target, not the proved constant. The lower bound is unconditional and elementary
(Parseval / averaging); the upper bound's input is the open BGK content. In the sparse regime the
open question is the `√(ln q)` gap between them.

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment ArkLib.ProximityGap.SecondMomentExact

namespace ArkLib.ProximityGap.SecondMomentLowerBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Non-trivial sup-norm lower bound.** Some `b ≠ 0` has `‖η_b‖² ≥ (q·|G| − |G|²)/(q−1)` — the average
of the DC-subtracted second moment over the `q−1` non-trivial frequencies. Hence
`M² ≥ n(q−n)/(q−1)`, which is `M ≥ √n·(1−o(1))` only when `n/q → 0`. -/
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
