/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R204 prize tower large-index arithmetic)
-/
import Mathlib

/-!
# R204 (#466): prize tower large-index arithmetic

R202 refuted medium-index universality, but the prize tower is not a
medium-index family: at the top level the quotient index is `2^128`, and every
descent from `n` to `n / 2` doubles the quotient index `(q - 1) / n`.

This file records the pure arithmetic needed by the R203 large-index route.
It does not assert any analytic Gauss-period estimate; it only prevents the
proof search from being distracted by finite medium-index counterexamples that
cannot appear on the prize-index tower.
-/

namespace ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex

/-- Quotient index after `depth` dyadic descents from a top quotient index
`Mtop`. -/
def DyadicTowerIndex (Mtop depth : ℕ) : ℕ :=
  Mtop * 2 ^ depth

/-- The quotient index is monotone along dyadic descent. -/
theorem le_dyadicTowerIndex (Mtop depth : ℕ) :
    Mtop ≤ DyadicTowerIndex Mtop depth := by
  unfold DyadicTowerIndex
  nth_rewrite 1 [← Nat.mul_one Mtop]
  exact Nat.mul_le_mul_left Mtop (Nat.succ_le_iff.mpr (Nat.two_pow_pos depth))

/-- Any lower bound true at the top remains true at every dyadic child. -/
theorem lowerBound_le_dyadicTowerIndex {N Mtop depth : ℕ}
    (hTop : N ≤ Mtop) :
    N ≤ DyadicTowerIndex Mtop depth :=
  hTop.trans (le_dyadicTowerIndex Mtop depth)

/-- Prize top index, as recorded in the dossier/workbench. -/
def PrizeTopIndex : ℕ :=
  2 ^ 128

/-- The R203 empirical large-index threshold is tiny compared with the prize
top quotient index. -/
theorem large1024_le_prizeTopIndex : 1024 ≤ PrizeTopIndex := by
  unfold PrizeTopIndex
  norm_num

/-- Every dyadic child of the prize-index tower is still in the R203
`1024`-large branch. -/
theorem large1024_le_prizeTowerIndex (depth : ℕ) :
    1024 ≤ DyadicTowerIndex PrizeTopIndex depth :=
  lowerBound_le_dyadicTowerIndex large1024_le_prizeTopIndex

/-- More generally, any threshold below `2^128` remains valid at every dyadic
child of the prize-index tower. -/
theorem threshold_le_prizeTowerIndex {N depth : ℕ}
    (hN : N ≤ PrizeTopIndex) :
    N ≤ DyadicTowerIndex PrizeTopIndex depth :=
  lowerBound_le_dyadicTowerIndex hN

end ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.le_dyadicTowerIndex
#print axioms ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.lowerBound_le_dyadicTowerIndex
#print axioms ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.large1024_le_prizeTopIndex
#print axioms ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.large1024_le_prizeTowerIndex
#print axioms ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.threshold_le_prizeTowerIndex
