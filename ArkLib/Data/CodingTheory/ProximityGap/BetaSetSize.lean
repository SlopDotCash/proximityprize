/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RimHookArea
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

/-!
# The β-set area is the partition size (#389)

Grounds the abstract `area` of `RimHookArea` as the genuine size of a partition. Writing the bead
set `B` (of `n` beads) in increasing order `β₀ < β₁ < … < β_{n-1}` via `Finset.orderEmbOfFin`, the
parts of the partition are `λ_j = β_j - j`, and:

> **`area_eq_sum_parts`** — `area B = ∑ⱼ (βⱼ - j)`, the sum of the partition's parts.

So `area B = |λ|` literally, confirming the rim-hook size law (`area_removeRimHook`) is a statement
about the number of cells removed. Axiom-clean.
-/

open Finset

namespace ArkLib.ProximityGap.BetaSetSize

open ArkLib.ProximityGap.RimHookArea

/-- The Gauss sum of the staircase: `∑_{j<n} j = C(n,2)`, as an integer. -/
theorem sum_fin_coe (n : ℕ) : ∑ j : Fin n, (j : ℤ) = (n.choose 2 : ℤ) := by
  have h : ∑ j : Fin n, ((j : ℕ)) = n.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id, Nat.choose_two_right]
  calc ∑ j : Fin n, (j : ℤ) = ((∑ j : Fin n, (j : ℕ) : ℕ) : ℤ) := by push_cast; rfl
    _ = (n.choose 2 : ℤ) := by rw [h]

/-- **The β-set area equals the partition size** `∑ⱼ (βⱼ - j)`. -/
theorem area_eq_sum_parts {B : Finset ℕ} {n : ℕ} (h : B.card = n) :
    area B = ∑ j : Fin n, ((B.orderEmbOfFin h j : ℤ) - (j : ℤ)) := by
  have hsum : ∑ b ∈ B, (b : ℤ) = ∑ j : Fin n, ((B.orderEmbOfFin h j : ℕ) : ℤ) := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ B h]
    rw [Finset.sum_image (fun x _ y _ hxy => (B.orderEmbOfFin h).injective hxy)]
  rw [Finset.sum_sub_distrib, ← hsum, sum_fin_coe, area, h]

end ArkLib.ProximityGap.BetaSetSize
