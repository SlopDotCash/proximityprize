/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.RankJohnsonComparison
import ArkLib.Research.ProximityGap.Frontier.FirstPrimeSepticCores
import ArkLib.Research.ProximityGap.Frontier.QuarterRateApolarBracket
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeLowRateExactPins
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeFourHeadEndpoints
import ArkLib.Research.ProximityGap.Frontier._ThreeCoreSecondPrimeBracket
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonPuncture
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-! # The finite Johnson radius on the two designated length-2³⁰ domains

Six MCA operational suprema lie strictly below the finite-length Johnson radius.
At the second prime and rate one eighth, the closed list at the first integer
error count strictly above Johnson still satisfies the list budget.
-/

namespace ProximityPrize.DesignatedPrimeJohnson

open Code ProximityGap ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap ArkLib.ProximityGap.Frontier
open scoped NNReal ENNReal

local instance : Fact PrizeShapePrimeP30.P.Prime := ⟨PrizeShapePrimeP30.prime_P⟩
local instance : Fact PrizeShapePrimeP30Second.P.Prime := ⟨PrizeShapePrimeP30Second.prime_P⟩

private abbrev n : ℕ := 2 ^ 30
private noncomputable abbrev tol : ℝ≥0∞ := 1 / (2 : ℝ≥0∞) ^ 128

/-- The finite-length Johnson radius uses the agreement degree `k-1`. -/
noncomputable def johnson (k : ℕ) : ℝ := 1 - Real.sqrt (((k - 1 : ℕ) : ℝ) / n)

/-- The operational line-MCA supremum on the supplied domain is strictly below Johnson. -/
def below {F : Type} [Field F] [Fintype F] (D : Fin n ↪ F) (k m : ℕ) : Prop :=
  (mcaDeltaStar (F := F) ((ReedSolomon.code D k : Set (Fin n → F)) ^⋈ (Fin m)) tol : ℝ) <
    johnson k

private theorem of_ceiling {F : Type} [Field F] [Fintype F] (D : Fin n ↪ F) (k m e : ℕ)
    [NeZero m] (he : e ≤ n) (hsq : n * (k - 1) < (n - e) ^ 2)
    (upper : mcaDeltaStar (F := F) (ReedSolomon.code D k : Set (Fin n → F)) tol ≤ (e : ℝ≥0) / n) :
    below D k m := by
  classical
  unfold below
  rw [mcaDeltaStar_interleaved_eq]
  have bound : ((mcaDeltaStar (F := F) (ReedSolomon.code D k : Set (Fin n → F)) tol : ℝ≥0) : ℝ) ≤
      (e : ℝ) / n := by exact_mod_cast upper
  refine bound.trans_lt ?_
  exact (RankJohnsonComparison.below_iff (n := n) (by decide) (k - 1)
    (some ⟨e, Nat.lt_succ_of_le he⟩)).mpr hsq

private theorem first_code (k : ℕ) (hk : 0 < k) :
    KKH26.evalCode PrizeShapePrimeP30.g n (k - 1) =
      (ReedSolomon.code FirstPrimeSepticCores.domain k :
        Set (Fin n → ZMod PrizeShapePrimeP30.P)) := by
  rw [KKH26RegimeSplit.evalCode_eq_reedSolomon PrizeShapePrimeP30.g
    PrizeShapePrimeP30.orderOf_g
    (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30.orderOf_g)]
  rw [Nat.sub_add_cancel hk]
  rfl

/-- On the actual first designated subgroup all four prize-rate MCA boundaries
are strictly below Johnson, at every positive width. -/
theorem first_four (m : ℕ) [NeZero m] :
    below FirstPrimeSepticCores.domain (2 ^ 29) m ∧ below FirstPrimeSepticCores.domain (2 ^ 28) m ∧
      below FirstPrimeSepticCores.domain (2 ^ 27) m ∧
      below FirstPrimeSepticCores.domain (2 ^ 26) m := by
  refine ⟨of_ceiling _ _ m 313174699 (by decide) (by decide) ?_,
    of_ceiling _ _ m 480946859 (by decide) (by decide) ?_,
    of_ceiling _ _ m 536870912 (by decide) (by decide) ?_,
    of_ceiling _ _ m 536870912 (by decide) (by decide) ?_⟩
  · rw [← first_code _ (by decide)]
    convert FirstPrimeSepticCores.threshold_le using 2 <;> norm_num [tol, epsStar, n]
  · rw [← first_code _ (by decide)]
    have h := QuarterRateApolarBracket.named_bracket.2
    rw [← P1RateQuarterCanonicalCodeBridge.evalCode_eq_canonicalCode] at h
    norm_num [tol, n, P1RateQuarterScaleArithmetic.N, P1RateQuarterScaleArithmetic.k] at h ⊢
    exact h
  · rw [← first_code _ (by decide)]
    have h := PrizeShapeLowRateExactPins.firstPrime_rateEighth_deltaStar_eq_half
    norm_num [tol, n] at h ⊢
    exact h.le
  · rw [← first_code _ (by decide)]
    have h := PrizeShapeLowRateExactPins.firstPrime_rateSixteenth_deltaStar_eq_half
    norm_num [tol, n] at h ⊢
    exact h.le

/-- On the actual second designated subgroup, the one-eighth and one-sixteenth
MCA boundaries are strictly below Johnson, at every positive width. -/
theorem second_lower_rates (m : ℕ) [NeZero m] :
    below SecondPrimeSmoothSeed.dom (2 ^ 27) m ∧ below SecondPrimeSmoothSeed.dom (2 ^ 26) m := by
  refine ⟨of_ceiling _ _ m 679477249 (by decide) (by decide) ?_,
    of_ceiling _ _ m 715827882 (by decide) (by decide) ?_⟩
  · have upper := (SecondPrimeFourHeadEndpoints.ceilings 1).1
    rwa [mcaDeltaStar_interleaved_eq] at upper
  · have h := ThreeCoreSecondPrimeBracket.secondPrime_ceiling (k := 2 ^ 26) (by decide) (by decide)
    rw [KKH26RegimeSplit.evalCode_eq_reedSolomon PrizeShapePrimeP30Second.g
      PrizeShapePrimeP30Second.orderOf_g
      (KKH26RegimeSplit.ne_zero_of_orderOf_eq PrizeShapePrimeP30Second.orderOf_g)] at h
    norm_num [tol, epsStar, n, SecondPrimeSmoothSeed.dom] at h ⊢
    exact h

/-- For every width and every injective domain of the designated length in the second field,
694116763 is the first integer error count strictly above Johnson at rate one eighth.
Even its closed ball contains at most 1660990722 codewords, within the 128-bit budget. -/
theorem second_eighth_list (D : Fin n ↪ ZMod PrizeShapePrimeP30Second.P) (m : ℕ) :
    (694116762 : ℝ) / n < johnson (2 ^ 27) ∧ johnson (2 ^ 27) < (694116763 : ℝ) / n ∧
      InterleavedListJohnsonRank.AtErrors D m (2 ^ 27) 694116763 1660990722 ∧
      1660990722 ≤ PrizeShapePrimeP30Second.P / 2 ^ 128 := by
  refine ⟨?_, ?_, InterleavedListJohnsonPuncture.eighth_below_johnson D m, by decide⟩
  · exact (RankJohnsonComparison.below_iff (n := n) (by decide) (2 ^ 27 - 1)
      (some ⟨694116762, by decide⟩)).mpr (by decide)
  · exact (RankJohnsonComparison.above_iff (n := n) (by decide) (2 ^ 27 - 1)
      (some ⟨694116763, by decide⟩)).mpr (by decide)

end ProximityPrize.DesignatedPrimeJohnson
