/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.StrictCoeffPolysShare

/-!
# The base case of the strict-coefficient share reduction (#389)

`StrictCoeffPolysShareResidual ℓ T` weakens the original strict-coefficient residual
`StrictCoeffPolysResidual` by allowing the recovered coefficient polynomials to match `P` on only a
*sub-share* `G' ⊆ good` of the good set, subject to the budget `|good| ≤ T + ℓ·|G'|`.  The trivial
corner `(ℓ, T) = (1, 0)` is the original residual: the budget `|good| ≤ |G'|` with `G' ⊆ good`
forces `G' = good`, so the share matching is matching on the whole good set.

Together with the proven reverse implication
`strictCoeffPolysShareResidual_of_strictCoeffPolysResidual`, this pins the `(1, 0)` corner of the
share family to the base residual — confirming the share family is a genuine *generalization*
(strictly weaker for `ℓ > 1` or `T > 0`) that degenerates exactly to the base at its trivial corner.
-/

set_option linter.unusedSectionVars false


open Finset
open scoped NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Base case of the share reduction.**  The share residual at the trivial share `ℓ = 1`,
budget `T = 0` implies the original (full-good-set) strict-coefficient residual: there `G' ⊆ good`
with `|good| ≤ 0 + 1·|G'|` forces `G' = good` (`Finset.eq_of_subset_of_card_le`), so the
coefficient-matching on `G'` is matching on the whole good set. -/
theorem strictCoeffPolysResidual_of_shareResidual_base {k deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (h : StrictCoeffPolysShareResidual (k := k) (deg := deg) (domain := domain) (δ := δ)
      (ℓ := 1) (T := 0)) :
    StrictCoeffPolysResidual (k := k) (deg := deg) (domain := domain) (δ := δ) := by
  intro hk u hprob hJ hsqrt P hP
  obtain ⟨B, G', hG'sub, hcard, hBdeg, hBid⟩ := h hk u hprob hJ hsqrt P hP
  have hGeq : G' = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ :=
    Finset.eq_of_subset_of_card_le hG'sub (by simpa using hcard)
  refine ⟨B, hBdeg, fun z hz j hj => ?_⟩
  exact hBid z (by rw [hGeq]; exact hz) j hj

end ProximityGap
