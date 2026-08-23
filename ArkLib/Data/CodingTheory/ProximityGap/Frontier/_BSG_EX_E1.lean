/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1

/-!
# BSG — DRC-extract sub-lemma `E1` (good-vertex neighbourhood is nonempty)

This file proves the first sub-lemma (`E1`) in the dependent-random-choice **extraction**
decomposition `BareDRCExtract` (the single remaining residual of the BGK chain, isolated in
`_BSG_DRC1.lean` and reduced to via `bareDRC_of_extract`).

`E1` says: given a *good* right-vertex `b₀` (one whose left-degree is large,
`#A ≤ 4·K²·rDeg A G b₀`), its left-neighbourhood `N = leftNbhd A G b₀` is **nonempty**.
This is needed because the conclusion of `BareDRCExtract` demands a nonempty subset `A'`, and the
canonical choice is `A' = N`.

The argument is elementary: if `rDeg A G b₀ = 0` then the good-vertex bound forces `#A ≤ 0`,
contradicting `A.Nonempty`; hence `rDeg A G b₀ > 0`, i.e. `#N > 0`.

## Status

`PROVEN` axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **`E1` (good-vertex neighbourhood is nonempty).** From the good-vertex bound
`#A ≤ 4·K²·rDeg A G b₀` and `A.Nonempty` (so `#A > 0`), the left-degree `rDeg A G b₀` is positive,
hence the left-neighbourhood `leftNbhd A G b₀` is nonempty. -/
theorem leftNbhd_b0_nonempty (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α)
    (hK : 0 < K) (hA : A.Nonempty) (hgood : #A ≤ 4 * K ^ 2 * rDeg A G b₀) :
    (leftNbhd A G b₀).Nonempty := by
  rw [← Finset.card_pos, card_leftNbhd]
  rcases Nat.eq_zero_or_pos (rDeg A G b₀) with h | h
  · exfalso
    rw [h, Nat.mul_zero] at hgood
    have := hA.card_pos
    omega
  · exact h

/-- The left-neighbourhood is always a subset of `A` (trivial; `leftNbhd` is a `filter` of `A`). -/
lemma leftNbhd_subset (A : Finset α) (G : Finset (α × α)) (b : α) :
    leftNbhd A G b ⊆ A :=
  Finset.filter_subset _ _

end Finset.BSG

#print axioms Finset.BSG.leftNbhd_b0_nonempty
#print axioms Finset.BSG.leftNbhd_subset
