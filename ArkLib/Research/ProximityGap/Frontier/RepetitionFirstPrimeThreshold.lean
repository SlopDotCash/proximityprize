/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.RepetitionSecondPrimeThreshold

/-! # Exact dimension-one MCA threshold at the first production prime -/
set_option autoImplicit false
noncomputable section
open Code
open scoped NNReal ENNReal
namespace ArkLib.ProximityGap.Frontier.RepetitionFirstPrimeThreshold
open _root_.ProximityGap _root_.ProximityGap.MCAThresholdLedger WeightedRichLinePacking

private abbrev n : ℕ := 1073741824
private abbrev p := PrizeShapePrimeP30.P
local instance : Fact p.Prime := ⟨PrizeShapePrimeP30.prime_P⟩

/-- Weighted line packing is within the integer security budget at 805,306,366 errors. -/
theorem predecessor (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] :
    epsMCA (F := ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (805306366/1073741824) ≤ 1/(2 : ℝ≥0∞)^128 := by
  have good := RepetitionSecondPrimeThreshold.probability_of_packing dom (by decide : 0 < 268435458)
    (by decide : 805306366 + 268435458 = n) Arrangement.first_predecessor width
  rw [ZMod.card] at good
  apply good.trans
  have h := (BoundarySecurityBudget.count_ratio_le_iff PrizeShapePrimeP30.prime_P.pos
    (by decide : 0 < 2^128)).mpr (by decide : 1073741824 ≤ p/2^128)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

/-- The two-center construction supplies 2³⁰+1 distinct bad challenges at the next count. -/
theorem failure (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] :
    1/(2 : ℝ≥0∞)^128 < epsMCA (F := ZMod p)
      ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (805306367/1073741824) := by
  have mass := RepeatedParabola.prime_mass (m := 2) (u := 268435456) (s := 536870912)
    (by decide) dom (by decide) width
  apply lt_of_lt_of_le _ mass
  by_contra! good
  have h := (BoundarySecurityBudget.count_ratio_le_iff PrizeShapePrimeP30.prime_P.pos
    (by decide : 0 < 2^128)).mp
      (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using good :
        ((2*536870912+1 : ℕ) : ℝ≥0∞)/p ≤ 1/((2^128 : ℕ) : ℝ≥0∞))
  exact (by decide : ¬ 2*536870912+1 ≤ p/2^128) h

/-- Every positive-width production-length repetition code at the first prime has this
operational supremum, on every injective evaluation domain. -/
theorem first_prime (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] :
    mcaDeltaStar (F := ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width))
      (1/(2 : ℝ≥0∞)^128) = 805306367/1073741824 := by
  have bad := failure dom width
  have good := predecessor dom width
  rw [epsMCA_interleaved_eq] at bad good
  rw [mcaDeltaStar_interleaved_eq]
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ bad)
  apply PrizeShapeRateHalfBracket.latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 805306367)
    (by decide) (by decide : 805306367 ≤ n)
  exact good

/-- Safety on every real nonnegative radius, including the failing boundary itself. -/
theorem safe_iff (dom : Fin n ↪ ZMod p) (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod p) ((ReedSolomon.code dom 1 : Set (Fin n → ZMod p)) ^⋈ (Fin width)) δ
      ≤ 1/(2 : ℝ≥0∞)^128 ↔ δ < 805306367/1073741824 := by
  constructor
  · intro good
    by_contra! large
    exact (failure dom width).not_ge ((epsMCA_mono _ large).trans good)
  · intro small
    by_contra! bad
    exact small.not_ge (first_prime dom width ▸ mcaDeltaStar_le_of_bad _ _ bad)

#print axioms safe_iff
#print axioms predecessor
#print axioms failure
#print axioms first_prime
end ArkLib.ProximityGap.Frontier.RepetitionFirstPrimeThreshold
