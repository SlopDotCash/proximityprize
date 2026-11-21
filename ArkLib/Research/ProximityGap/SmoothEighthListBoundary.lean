/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.SmoothPrizeCapacityTable
import ArkLib.Research.ProximityGap.Frontier.BlsScalarListThreshold

/-! # The sharp uniform rate-one-eighth list boundary

Among smooth domains of length at least 256 over fields with fewer than
`2^256` elements, the largest operational list threshold at 128-bit tolerance
is `223/256`. The order-256 BLS12-381 scalar subgroup attains this supremum
at every positive width. The individual closed ball at that radius already fails.
-/

namespace ProximityPrize.SmoothEighthListBoundary

open Code ProximityGap ProximityGap.GrandChallenges
open scoped NNReal ENNReal

/-- From precisely this radius onward every supplied code in the family exceeds
the actual closed-list budget. Below it the BLS12-381 example still passes. -/
theorem all_fail_iff (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    (∀ (F I : Type) [Field F] [Fintype F] [DecidableEq F] [Fintype I] [Nonempty I]
      (D : I ↪ F) [ReedSolomon.Smooth D], 256 ≤ Fintype.card I → Fintype.card F < 2 ^ 256 →
      ((prizeThreshold : ℝ≥0) : ℝ≥0∞) * Fintype.card F <
        (Lambda (ListInterpolationBoundary.words D (Fintype.card I / 8) width) (δ : ℝ) : ℝ≥0∞)) ↔
      223 / 256 ≤ δ := by
  constructor
  · intro all
    by_contra! low
    let K := ZMod BlsScalarSubgroup.P
    have bad := all K BlsScalarListThreshold.H BlsScalarListThreshold.domain
      BlsScalarListThreshold.card_H.ge (by change Fintype.card (ZMod _) < _; rw [ZMod.card]; decide)
    rw [BlsScalarListThreshold.card_H] at bad
    exact bad.not_ge ((BlsScalarListThreshold.rateEighth width (NeZero.pos width) δ).mpr
      (by exact_mod_cast low))
  · intro lower F I _ _ _ _ _ D _ len field
    exact (SmoothPrizeCapacityTable.failures D (2 : Fin 4) width len field lower).2

end ProximityPrize.SmoothEighthListBoundary
