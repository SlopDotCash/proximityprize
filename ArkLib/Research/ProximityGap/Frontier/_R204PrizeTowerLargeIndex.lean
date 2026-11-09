/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (R204 prize tower large-index arithmetic)
-/
import Mathlib
import ArkLib.Research.ProximityGap.Frontier._BGKJacobiTensorProductionGap

/-!
# R204 (#466): prize tower large-index arithmetic

R202 refuted medium-index universality, but the prize tower is not a
medium-index family: at the top level (`n = 2^30`) the quotient index is the
certified production value `m = (q - 1) / n = 2^128 + 192` (not the rough proxy
`2^128`), and every descent from `n` to `n / 2` doubles the quotient index
`(q - 1) / n`.

**Correction (audit R-034, 2026-10-28).** `PrizeTopIndex` was previously defined
as exactly `2^128`.  Since consumers require the *equality*
`s.card = DyadicTowerIndex PrizeTopIndex depth`, that proxy could never be met by
the actual production quotient (whose index `2^128 + 192` is not a power of two).
It is now the certified value `productionM = 2^128 + 192`
(`prizeTopIndex_eq_productionM`).  The `1024` lower threshold is unaffected.

*Quotient versus raw carriers.*  `DyadicTowerIndex PrizeTopIndex k` is the
number of cosets of the depth-`k` child `μ_{2^(30-k)}` in `F^×`.  The **raw**
nonzero carrier `F^×` has cardinality `q - 1 = DyadicTowerIndex PrizeTopIndex 30`
(`productionQ_sub_one_eq_dyadicTowerIndex_thirty`): a raw-carrier equality
`(nonzeroFreqs).card = DyadicTowerIndex PrizeTopIndex depth` can hold at
production only at `depth = 30`, i.e. the quotient by the trivial subgroup, not
at the quotient depth of a nontrivial child.  The full field `univ` has odd
cardinality `q` and can never equal a dyadic tower index of even top index.

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

/-- Prize top quotient index: the certified production value
`m = (q - 1) / 2^30 = 2^128 + 192` for `q = productionQ`. -/
def PrizeTopIndex : ℕ :=
  2 ^ 128 + 192

open ArkLib.ProximityGap.Frontier.BGKJacobiTensorProductionGap in
/-- `PrizeTopIndex` is exactly the production multiplicative index `productionM`. -/
theorem prizeTopIndex_eq_productionM : PrizeTopIndex = productionM := rfl

open ArkLib.ProximityGap.Frontier.BGKJacobiTensorProductionGap in
/-- The raw nonzero production carrier has cardinality `q - 1`, which is the dyadic tower
index at depth `30` (the quotient by the trivial subgroup), not at the depth of a nontrivial
child. -/
theorem productionQ_sub_one_eq_dyadicTowerIndex_thirty :
    productionQ - 1 = DyadicTowerIndex PrizeTopIndex 30 := by
  unfold productionQ productionN productionM DyadicTowerIndex PrizeTopIndex
  rw [Nat.add_sub_cancel, Nat.mul_comm]

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

/-- More generally, any threshold below `PrizeTopIndex = 2^128 + 192` remains valid at every
dyadic child of the prize-index tower. -/
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
#print axioms
  ArkLib.ProximityGap.Frontier.R204PrizeTowerLargeIndex.productionQ_sub_one_eq_dyadicTowerIndex_thirty
