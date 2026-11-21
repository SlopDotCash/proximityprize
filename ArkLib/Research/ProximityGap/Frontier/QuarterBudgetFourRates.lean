/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ArkLib.Research.ProximityGap.Frontier.ApolarMovingCount
import ArkLib.Research.ProximityGap.Frontier.RateHalfApolarThreshold
import ArkLib.Research.ProximityGap.Frontier.RateQuarterApolarBudget
import ArkLib.Research.ProximityGap.Frontier._TwoCorePackingThreshold
import ArkLib.Research.ProximityGap.Frontier._HalfPredecessorBadEventRichPointBridge

/-! # Four operational radii for a production-length field of quarter-rate budget

The code has length 2³⁰. The field budget is 3·2²⁷. At half rate the
bisimplex breaks soundness at radius 1/4. Every other prize rate has its
first bad Hamming count at the budget itself.
-/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier.RateQuarterApolarBudget
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.QuarterBudgetFourRates

private abbrev n : ℕ := 1073741824
private abbrev B : ℕ := 402653184
noncomputable abbrev code (k : ℕ) := evalCode generator n (k-1)

private theorem predecessor_good_of_count {k e : ℕ} (hk : 1 ≤ k)
    (hcount : ∀ (dom : Fin n ↪ ZMod P) (u : Code.WordStack (ZMod P) (Fin 2) (Fin n)),
      let δ : ℝ≥0 := (e : ℝ≥0)/n
      let fam := canonicalBadScalarRichPointFamily dom δ u hk
      fam.G.card ≤ B) :
    epsMCA (F := ZMod P) (code k) ((e:ℝ≥0)/n) ≤ (epsStar:ℝ≥0∞) := by
  classical
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq generator_order
  let dom := KKH26RegimeSplit.powDomain generator generator_order hg0
  have hcode : code k = (ReedSolomon.code dom k : Set (Fin n → ZMod P)) := by
    simpa only [code,dom,show k-1+1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon generator generator_order hg0 (k-1)
  rw [hcode,epsStar_coe_eq_natCast_inv]
  apply (epsMCA_le_of_badCount_le _ _ B ?_).trans
  · rw [ZMod.card]
    exact natCast_div_le_inv_of_mul_le (Q := 2^128) (by decide) prime_P.pos (by decide)
  · intro u
    simpa only [canonicalBadScalarRichPointFamily,badScalars] using hcount dom u

private theorem quarter_spike {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 268435456) :
    (epsStar:ℝ≥0∞) < epsMCA (F := ZMod P) (code k) (3/8) := by
  let dom := Ownership.smoothDom generator n generator_order
  let positions : Fin 402653185 ↪ Fin n := Fin.castLEEmb (by decide)
  have spike := SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode dom k)
    (SpikeFloor.rsCode_noWeightLE dom (show 402653185+k ≤ n by dsimp [n]; omega))
    (δ := (3/8:ℝ≥0)) (by norm_num) (by decide) (by rw [Fintype.card_fin]; decide)
    positions (positions.trans dom) (b := (1:ZMod P)) one_ne_zero
  rw [ZMod.card] at spike
  rw [code,Ownership.evalCode_pred_eq_rsCode generator_order hk,epsStar_coe_eq_natCast_inv]
  apply lt_of_lt_of_le _ spike
  have hp : (P:ℝ≥0∞) ≠ 0 := by exact_mod_cast prime_P.ne_zero
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top P)),
    ← ENNReal.div_eq_inv_mul,
    ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast (show P < 402653185*2^128 by decide)

private theorem threshold_half_of_good
    (safe : epsMCA (F := ZMod P) (code 536870912) ((268435455:ℝ≥0)/n) ≤ (epsStar:ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod P) (code 536870912) (epsStar:ℝ≥0∞) = 1/4 := by
  apply le_antisymm
  · exact mcaDeltaStar_le_of_bad _ _ (RateHalfApolarThreshold.endpoint_bad generator_order
      (by rw [budget];decide))
  · have h := latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := 268435456)
      (by decide) (by decide : 268435456 ≤ n) _ _ safe
    rwa [show ((268435456:ℕ):ℝ≥0)/n = 1/4 by norm_num [n]] at h

private theorem threshold_low_of_good {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 268435456)
    (safe : epsMCA (F := ZMod P) (code k) ((402653183:ℝ≥0)/n) ≤ (epsStar:ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod P) (code k) (epsStar:ℝ≥0∞) = 3/8 := by
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ (quarter_spike hk hk'))
  have h := latticeBoundary_le_mcaDeltaStar_of_predecessor_good (a := B)
    (by decide) (by decide : B ≤ n) _ _ safe
  rwa [show (B:ℝ≥0)/n = 3/8 by norm_num [n,B]] at h

/-- Uniform good side whenever the simple spike count fits the field and the
rank-count slack is at least three. -/
theorem predecessor_good {k e : ℕ} (hk : 1 ≤ k) (he : e ≤ n)
    (hkfit : k+e < n) (hslack : 2*e+k+2 ≤ n) (hfit : e+1 ≤ B) :
    epsMCA (F := ZMod P) (code k) ((e:ℝ≥0)/n) ≤ (epsStar:ℝ≥0∞) := by
  classical
  apply predecessor_good_of_count hk
  intro dom u
  let δ : ℝ≥0 := (e:ℝ≥0)/n
  let fam := canonicalBadScalarRichPointFamily dom δ u hk
  let d := n-k-1
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin _
  have hagree : Fintype.card (Fin n) - e ≤ ⌈(1-δ)*(Fintype.card (Fin n):ℝ≥0)⌉₊ := by
    rw [show ⌈(1-δ)*(Fintype.card (Fin n):ℝ≥0)⌉₊ = n-e from
      TwoCorePackingThreshold.agreement_ceiling e he,hcard]
  have hc := _root_.ProximityGap.ApolarMovingCount.count_mca_family
    (algebraMap (ZMod P) (AlgebraicClosure (ZMod P))) fam fam.G (Finset.Subset.rfl)
    (e:=e) (d:=d) (by dsimp [d]; omega) (by dsimp [d];omega) hk
    (by rw [hcard];dsimp [d];omega) hagree
  change fam.G.card ≤ B
  obtain hs | hm := hc
  · exact hs.trans hfit
  · have hthree : 3 ≤ d+2-2*e := by dsimp [d];omega
    have hprod := (Nat.mul_le_mul_left (fam.G.card-1) hthree).trans hm
    rw [hcard] at hprod
    dsimp only [n,B] at *
    omega

/-- The first bad radius at half rate, with an unconditional safe predecessor. -/
theorem half_rate :
    mcaDeltaStar (F := ZMod P) (code 536870912) (epsStar:ℝ≥0∞) = 1/4 :=
  threshold_half_of_good (predecessor_good (by decide) (by decide) (by decide) (by decide)
    (by decide))

/-- Every positive dimension through one quarter has first bad radius 3/8. -/
theorem through_quarter {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ 268435456) :
    mcaDeltaStar (F := ZMod P) (code k) (epsStar:ℝ≥0∞) = 3/8 := by
  apply threshold_low_of_good hk hk'
  apply predecessor_good hk (by decide) (by dsimp [n];omega) (by dsimp [n];omega) (by decide)

/-- The four exact operational radii at the official rates for this field. -/
theorem four_rates :
    mcaDeltaStar (F := ZMod P) (code (2^29)) (epsStar:ℝ≥0∞) = 1/4 ∧
    mcaDeltaStar (F := ZMod P) (code (2^28)) (epsStar:ℝ≥0∞) = 3/8 ∧
    mcaDeltaStar (F := ZMod P) (code (2^27)) (epsStar:ℝ≥0∞) = 3/8 ∧
    mcaDeltaStar (F := ZMod P) (code (2^26)) (epsStar:ℝ≥0∞) = 3/8 :=
  ⟨half_rate,through_quarter (by decide) (by decide),through_quarter (by decide) (by decide),
    through_quarter (by decide) (by decide)⟩

/-- Under every positive interleaving width the first bad point and the strict
good region remain the same throughout the four-rate table. -/
theorem interleaved_good_iff {k : ℕ} (hk : 1 ≤ k)
    (hcase : k=536870912 ∨ k≤268435456) (width : ℕ) [NeZero width] (δ : ℝ≥0) :
    let radius : ℝ≥0 := if k=536870912 then 1/4 else 3/8
    epsMCA (F := ZMod P) (A := Fin width → ZMod P) ((code k) ^⋈ (Fin width)) δ ≤
      (epsStar:ℝ≥0∞) ↔ δ < radius := by
  let radius : ℝ≥0 := if k=536870912 then 1/4 else 3/8
  have hc := Ownership.evalCode_pred_eq_rsCode generator_order hk
  unfold code
  rw [hc,epsMCA_interleaved_eq,← hc]
  have star : mcaDeltaStar (F := ZMod P) (code k) (epsStar:ℝ≥0∞) = radius := by
    rcases hcase with rfl | small
    · simpa [radius] using half_rate
    · simpa [radius,show k ≠ 536870912 by omega] using through_quarter hk small
  have hs : mcaDeltaStar (F := ZMod P) (code k) (epsStar:ℝ≥0∞) < 1 := by
    rw [star]
    dsimp [radius]
    split <;> norm_num
  change epsMCA (F := ZMod P) (code k) δ ≤ _ ↔ δ < radius
  rw [← star]
  constructor
  · intro good
    by_contra! h
    exact (MCAStepFunction.lt_epsMCA_mcaDeltaStar_of_lt_one _ _ hs).not_ge
      ((epsMCA_mono _ h).trans good)
  · intro h
    by_contra! bad
    exact h.not_ge (mcaDeltaStar_le_of_bad _ _ bad)

#print axioms interleaved_good_iff
#print axioms predecessor_good
#print axioms half_rate
#print axioms through_quarter
#print axioms four_rates

end ArkLib.ProximityGap.Frontier.QuarterBudgetFourRates
