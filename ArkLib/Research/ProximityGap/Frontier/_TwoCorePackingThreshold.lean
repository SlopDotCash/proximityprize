/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._TwoCoreMomentApplication
import ArkLib.Research.ProximityGap.Frontier._PrizeShapeRateHalfBracket
import ArkLib.Research.ProximityGap.Frontier._PackingBudgetFirstJump

/-!
# Thresholds from the production two-core count

At length `2^30`, the two-core estimate bounds the exceptional scalar count
by `2e+2` at integer error count `e` throughout its agreement window.
Pairing that cap with overlap packing determines the threshold whenever the
budget crossing lies in the window.
-/

open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.TwoCorePackingThreshold

open PrizeShapeRateHalfBracket

/-- The production block length. -/
abbrev domainLength : ℕ := 1073741824

/-- Exact agreement ceiling for an integer error count on the production domain. -/
theorem agreement_ceiling (e : ℕ) (_he : e ≤ domainLength) :
    ⌈(1 - (e : ℝ≥0) / (domainLength : ℝ≥0)) * (Fintype.card (Fin domainLength) : ℝ≥0)⌉₊ =
      domainLength - e := by
  rw [Fintype.card_fin, tsub_mul, one_mul, div_mul_cancel₀ _ (by norm_num [domainLength])]
  have h : (domainLength : ℝ≥0) - (e : ℝ≥0) = ((domainLength - e : ℕ) : ℝ≥0) := by
    rw [Nat.cast_tsub]
  rw [h, Nat.ceil_natCast]

/-- The normalized two-core upper bound on the original smooth code. -/
theorem epsMCA_le_twoCore_count {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (hlo : 426115517 ≤ domainLength - e) (hhi : domainLength - e ≤ 570425344) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (k - 1))
      ((e : ℝ≥0) / (domainLength : ℝ≥0)) ≤ ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  let δ : ℝ≥0 := (e : ℝ≥0) / (domainLength : ℝ≥0)
  have he : e ≤ domainLength := by omega
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom := KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g domainLength (k - 1) =
      (ReedSolomon.code dom k : Set (Fin domainLength → ZMod p)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 (k - 1)
  rw [hcode]
  refine (epsMCA_le_of_badCount_le _ _ (2 * e + 2) ?_).trans (by rw [ZMod.card])
  intro u
  have hf := TwoCoreMomentApplication.production_family_card_le
    (canonicalBadScalarRichPointFamily dom (k := k) δ u hk) (e := e) (t := domainLength - e)
    (Fintype.card_fin _) (by change e + (domainLength - e) = domainLength; omega)
    hk hkmax (agreement_ceiling e he) hlo hhi
  simpa only [canonicalBadScalarRichPointFamily, badScalars, δ] using hf

/-- The exact error throughout the overlap between the two-core estimate and packing. -/
theorem epsMCA_eq_twoCore_count {p k e : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hk : 2 ≤ k) (hkmax : k ≤ 67108864)
    (hehalf : domainLength ≤ 2 * e) (hlo : 426115517 ≤ domainLength - e)
    (hfresh : 2 * (2 * e - domainLength + 2) ≤ p - domainLength) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g domainLength (k - 1))
      ((e : ℝ≥0) / (domainLength : ℝ≥0)) =
      ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  have hhi : domainLength - e ≤ 570425344 := by dsimp [domainLength] at hehalf ⊢; omega
  apply le_antisymm (epsMCA_le_twoCore_count hg (by omega) hkmax hlo hhi)
  have hcap : e + k + 1 ≤ domainLength := by dsimp [domainLength] at hlo ⊢; omega
  have h := PackingBudgetFirstJump.overlap_epsMCA_lower_bound_of_supply
    hg hk hehalf hcap hfresh
  have he : e ≤ domainLength := by omega
  have hn : (domainLength : ℝ≥0) ≠ 0 := by norm_num [domainLength]
  have hbound : (e : ℝ≥0) / domainLength ≤ 1 :=
    (div_le_one (pos_iff_ne_zero.mpr hn)).2 (by exact_mod_cast he)
  have hsub : ((domainLength - e : ℕ) : ℝ≥0) / domainLength = 1 - (e : ℝ≥0) / domainLength := by
    rw [Nat.cast_tsub, tsub_div, div_self hn]
  rwa [hsub, tsub_tsub_cancel_of_le hbound] at h

/-- Good-side threshold at the first lattice point above a two-core count that fits the budget. -/
theorem threshold_lower_of_twoCore_count {p k e Q : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hk : 1 ≤ k) (hkmax : k ≤ 67108864)
    (hlo : 426115517 ≤ domainLength - e) (hhi : domainLength - e ≤ 570425344)
    (hQ : 0 < Q) (hbudget : 2 * e + 2 ≤ p / Q) :
    ((e + 1 : ℕ) : ℝ≥0) / (domainLength : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g domainLength (k - 1)) (Q : ℝ≥0∞)⁻¹ := by
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by omega) (by omega)
  have h := epsMCA_le_twoCore_count hg hk hkmax hlo hhi
  simp only [predecessorRadius, Nat.add_sub_cancel]
  refine h.trans (natCast_div_le_inv_of_mul_le hQ (Fact.out (p := p.Prime)).pos ?_)
  exact (Nat.mul_le_mul_right Q hbudget).trans (Nat.div_mul_le_self p Q)

/-- Complete rate-one-sixteenth threshold when the half-budget is between one half the
length and the last lattice step certified by the two-core estimate. -/
theorem rateSixteenth_window {p : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = domainLength) (hlo : 536870912 ≤ (p / 2 ^ 128) / 2)
    (hhi : (p / 2 ^ 128) / 2 ≤ 647626308) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g domainLength (2 ^ 26 - 1))
      (ProximityGap.epsStar : ℝ≥0∞) =
      (((p / 2 ^ 128) / 2 : ℕ) : ℝ≥0) / (domainLength : ℝ≥0) := by
  let B := p / 2 ^ 128
  let e := B / 2
  change 536870912 ≤ e at hlo
  change e ≤ 647626308 at hhi
  have hBe : 2 * e ≤ B ∧ B ≤ 2 * e + 1 := by dsimp only [e]; omega
  have hbig : 2 * B ≤ p := by
    calc
      2 * B ≤ 2 ^ 128 * B := Nat.mul_le_mul_right B (by norm_num)
      _ = B * 2 ^ 128 := Nat.mul_comm _ _
      _ ≤ p := Nat.div_mul_le_self _ _
  have hbudget : 2 * (e - 1) + 2 ≤ B := by omega
  rw [epsStar_coe_eq_natCast_inv]
  apply le_antisymm
  · have hmax : max ((domainLength - 2 ^ 26) / 2) ((p / 2 ^ 128) / 2) = e := by
      apply max_eq_right
      change (domainLength - 2 ^ 26) / 2 ≤ e
      dsimp [domainLength]
      omega
    have hus := PackingBudgetFirstJump.mcaDeltaStar_le_first_deep_packing_of_floor_budget
      (Q := 2 ^ 128) (k := 2 ^ 26) hg (by norm_num) (by norm_num) (by norm_num [domainLength])
      (show domainLength ≤ B by dsimp [domainLength]; omega)
      (show B ≤ 2 * (domainLength - 2 ^ 26) - 1 by dsimp [domainLength]; omega)
      (by dsimp only; rw [hmax]; dsimp [domainLength]; omega)
    dsimp only at hus
    rw [hmax] at hus
    have he : e ≤ domainLength := by dsimp [domainLength]; omega
    have hfrac : ((domainLength - e : ℕ) : ℝ≥0) / (domainLength : ℝ≥0) ≤ 1 := by
      apply (div_le_one (by norm_num [domainLength])).2
      exact_mod_cast Nat.sub_le domainLength e
    have hsum : e + (domainLength - e) = domainLength := by omega
    have hr : (1 : ℝ≥0) - ((domainLength - e : ℕ) : ℝ≥0) / (domainLength : ℝ≥0) =
        (e : ℝ≥0) / domainLength := by
      rw [tsub_eq_iff_eq_add_of_le hfrac, ← add_div, ← Nat.cast_add, hsum,
        div_self (by norm_num [domainLength])]
    rwa [hr] at hus
  · have h := threshold_lower_of_twoCore_count (e := e - 1) (k := 2 ^ 26) (Q := 2 ^ 128)
      hg (by norm_num) (by norm_num) (by dsimp [domainLength]; omega)
      (by dsimp [domainLength]; omega)
      (by norm_num) hbudget
    simpa only [show e - 1 + 1 = e by omega] using h

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The second repository prime supplies twice the length as its scalar budget. The last
covered error of the two-core bound gives the following improved floor. -/
theorem secondPrime_rateSixteenth_floor :
    (647626308 / 1073741824 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g domainLength (2 ^ 26 - 1))
        (ProximityGap.epsStar : ℝ≥0∞) := by
  rw [epsStar_coe_eq_natCast_inv]
  have h := threshold_lower_of_twoCore_count (e := 647626307) (k := 2 ^ 26) (Q := 2 ^ 128)
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g (by norm_num) (by norm_num)
    (by norm_num [domainLength]) (by norm_num [domainLength]) (by norm_num)
    (by rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P_div_two_pow_128]; norm_num)
  exact h

#print axioms epsMCA_le_twoCore_count
#print axioms epsMCA_eq_twoCore_count
#print axioms rateSixteenth_window
#print axioms secondPrime_rateSixteenth_floor

end ArkLib.ProximityGap.Frontier.TwoCorePackingThreshold
