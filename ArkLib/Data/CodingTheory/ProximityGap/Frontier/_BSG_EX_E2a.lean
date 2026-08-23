/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1
import Mathlib.Tactic.Linarith

/-!
# BSG / DRC extraction — sub-lemma E2a: unpack cherry-richness

This is the `prep` step of the dependent-random-choice extraction (`BareDRCExtract`). It cancels
one factor of `#A` from the *cherry-richness* hypothesis

  `#A⁴ ≤ 16 K⁴ · (#A · ∑_b deg(b)²)`

to obtain the clean cherry lower bound

  `#A³ ≤ 16 K⁴ · ∑_b deg(b)²`.

This is exactly the `hcube` step already proven inside `exists_large_left_neighborhood`
(`_BSG_DRC2.lean`); it is reproduced here as a standalone named lemma so the E2/E3 refinement
pipeline can consume it directly. The total cherry mass `∑deg² ≥ #A³/(16K⁴) = #A²·(#A/(16K⁴))`
means that, with threshold `t := #A/(32K⁴)` (half the per-pair average), the total exceeds `#A²·2t`.

## Status

`PROVEN` — axiom-clean (`propext, Classical.choice, Quot.sound`), no `sorry`.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- **E2a (cherry-richness unpacking, PROVEN).** Cancel one factor of `#A` (nonempty) from the
cherry-richness hypothesis `#A⁴ ≤ 16 K⁴ · (#A · ∑_b deg(b)²)` to get the clean cherry lower bound
`#A³ ≤ 16 K⁴ · ∑_b deg(b)²`. This is the `hcube` step of `exists_large_left_neighborhood`. -/
theorem cherry_ge_of_richness (A : Finset α) (K : ℕ) (hK : 0 < K) (G : Finset (α × α))
    (hA : A.Nonempty)
    (hcherry : #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2))) :
    #A ^ 3 ≤ 16 * K ^ 4 * (∑ b ∈ A, rDeg A G b ^ 2) := by
  have hApos : 0 < #A := hA.card_pos
  have hfac : #A * #A ^ 3 ≤ #A * (16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2) := by
    calc #A * #A ^ 3 = #A ^ 4 := by ring
      _ ≤ 16 * K ^ 4 * (#A * ∑ b ∈ A, rDeg A G b ^ 2) := hcherry
      _ = #A * (16 * K ^ 4 * ∑ b ∈ A, rDeg A G b ^ 2) := by ring
  exact Nat.le_of_mul_le_mul_left hfac hApos

end Finset.BSG
