/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.RateQuarterPairOverlap
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarBudget
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAStepFunction

/-! # Exact operational radii for the three lower rates at the boundary prime -/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier.RateHalfApolarBudget.Boundary
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.BoundaryLowerRates

abbrev n : ℕ := 1073741824
abbrev firstBad : ℕ := 268435458
noncomputable abbrev radius : ℝ≥0 := (firstBad : ℝ≥0) / n
noncomputable abbrev code (k : ℕ) := evalCode generator n (k - 1)

/-- At the predecessor every received pair has at most the budgeted number of
bad scalars, uniformly for all positive dimensions up to one quarter. -/
theorem predecessor_good {k : ℕ} (hk : 1 ≤ k) (hmax : k ≤ 268435456) :
    epsMCA (F := ZMod P) (code k) ((268435457 : ℝ≥0) / n) ≤ (epsStar : ℝ≥0∞) := by
  classical
  let δ : ℝ≥0 := (268435457 : ℝ≥0) / n
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq generator_order
  let dom := KKH26RegimeSplit.powDomain generator generator_order hg0
  have hcode : code k = (ReedSolomon.code dom k : Set (Fin n → ZMod P)) := by
    simpa only [code, dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon generator generator_order hg0 (k - 1)
  rw [hcode, epsStar_coe_eq_natCast_inv]
  apply (epsMCA_le_of_badCount_le _ _ firstBad ?_).trans
  · rw [ZMod.card]
    exact natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide) prime_P.pos (by decide)
  · intro u
    have ht : ⌈(1-δ) * (Fintype.card (Fin n) : ℝ≥0)⌉₊ = 805306367 :=
      TwoCorePackingThreshold.agreement_ceiling 268435457 (by decide)
    have hf := RateQuarterPairOverlap.family_card_le
      (canonicalBadScalarRichPointFamily dom (k := k) δ u hk) (Fintype.card_fin _) hk hmax ht
    simpa only [canonicalBadScalarRichPointFamily, badScalars, δ] using hf

/-- The next Hamming step admits one more spike scalar than the field budget. -/
theorem endpoint_bad {k : ℕ} (hk : 1 ≤ k) (hmax : k ≤ 268435456) :
    (epsStar : ℝ≥0∞) < epsMCA (F := ZMod P) (code k) radius := by
  let dom := Ownership.smoothDom generator n generator_order
  let positions : Fin 268435459 ↪ Fin n := Fin.castLEEmb (by decide)
  have spike := SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode dom k)
    (SpikeFloor.rsCode_noWeightLE dom (show 268435459 + k ≤ n by dsimp [n]; omega))
    (δ := radius) (by norm_num [radius, firstBad, n]) (by decide)
    (by rw [Fintype.card_fin]; decide) positions (positions.trans dom)
    (b := (1 : ZMod P)) one_ne_zero
  rw [ZMod.card] at spike
  rw [code, Ownership.evalCode_pred_eq_rsCode generator_order hk, epsStar_coe_eq_natCast_inv]
  apply lt_of_lt_of_le _ spike
  have hp : (P : ℝ≥0∞) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top P)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast (show P < 268435459 * 2^128 by decide)

/-- The first bad real-radius boundary for every dimension through quarter rate. -/
theorem threshold {k : ℕ} (hk : 1 ≤ k) (hmax : k ≤ 268435456) :
    mcaDeltaStar (F := ZMod P) (code k) (epsStar : ℝ≥0∞) = radius := by
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ (endpoint_bad hk hmax))
  exact latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := firstBad)
    (by decide) (by decide : firstBad ≤ n) _ _ (predecessor_good hk hmax)

/-- The full good-radius predicate, including failure at the supremum. -/
theorem good_iff {k : ℕ} (hk : 1 ≤ k) (hmax : k ≤ 268435456) (δ : ℝ≥0) :
    epsMCA (F := ZMod P) (code k) δ ≤ (epsStar : ℝ≥0∞) ↔ δ < radius := by
  constructor
  · intro hgood
    by_contra! h
    exact (endpoint_bad hk hmax).not_ge ((epsMCA_mono _ h).trans hgood)
  · intro h
    by_contra! hbad
    have bound := mcaDeltaStar_le_of_bad _ _ hbad
    rw [threshold hk hmax] at bound
    exact h.not_ge bound

/-- The exact scalar thresholds at rates one quarter, one eighth and one sixteenth. -/
theorem three_rates :
    mcaDeltaStar (F := ZMod P) (code (2^28)) (epsStar : ℝ≥0∞) = radius ∧
    mcaDeltaStar (F := ZMod P) (code (2^27)) (epsStar : ℝ≥0∞) = radius ∧
    mcaDeltaStar (F := ZMod P) (code (2^26)) (epsStar : ℝ≥0∞) = radius :=
  ⟨threshold (by decide) (by decide), threshold (by decide) (by decide),
    threshold (by decide) (by decide)⟩

/-- Every positive interleaving width has the same real good-radius interval. -/
theorem interleaved_good_iff {k : ℕ} (hk : 1 ≤ k) (hmax : k ≤ 268435456)
    (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    epsMCA (F := ZMod P) (A := Fin width → ZMod P) ((code k) ^⋈ (Fin width)) δ ≤
      (epsStar : ℝ≥0∞) ↔ δ < radius := by
  have hc := Ownership.evalCode_pred_eq_rsCode generator_order hk
  unfold code
  rw [hc, epsMCA_interleaved_eq, ← hc]
  exact good_iff hk hmax δ

#print axioms predecessor_good
#print axioms endpoint_bad
#print axioms threshold
#print axioms three_rates
#print axioms interleaved_good_iff

end ArkLib.ProximityGap.Frontier.BoundaryLowerRates
