/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateEighthFullWiring
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._HalfPredecessorRateSixteenthPin

/-!
# Operational rate-1/8 pin from the half-predecessor incidence bound

This file normalizes the rate-`1/8` canonical rich-point bound by the field size and combines
the resulting half-predecessor good side with the overlap-packing upper bound.  At a tight
field-normalized budget, the operational MCA threshold is exactly `1/2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal
open _root_.ProximityGap Code ProximityGap.MCAThresholdLedger
open ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.PackingBudgetFirstJump
open ArkLib.ProximityGap.Frontier.R382HalfRadiusPinConnector
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateSixteenthPin

namespace ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The literal rate-`1/8` rich-point bound, normalized by the field size. -/
theorem epsMCA_halfPredecessor_rateEighth_le
    {n h k : ℕ} [NeZero n] (dom : Fin n ↪ F)
    (hn : n = 2 * h) (hh : 2048 ≤ h) (hk : 1 ≤ k)
    (hrate : 8 * k ≤ n) :
    epsMCA (F := F) (A := F)
        ((ReedSolomon.code dom k : Set (Fin n → F)))
        (halfPredecessorRadius n) ≤
      (n : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  apply epsMCA_halfPredecessor_le_of_canonicalRichPointFamily_card_le dom hk
  intro u
  exact
    HalfPredecessorRateEighthFullWiring.canonical_halfPredecessor_card_le_length
      dom hn hh hk hrate u

open Classical in
/-- At rate at most `1/8`, the half-predecessor count and overlap packing pin the operational
MCA threshold exactly at `1/2`. -/
theorem evalCode_mcaDeltaStar_eq_half_of_rateEighth
    {p n h k Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n)
    (hQ : 0 < Q) (hk : 2 ≤ k)
    (hn : n = 2 * h) (hh : 2048 ≤ h)
    (hfloor : p / Q = n) (hrate : 8 * k ≤ n)
    (hsupply : 4 ≤ p - n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) =
      (1 / 2 : ℝ≥0) := by
  have hnEven : n % 2 = 0 := by omega
  have hg0 : g ≠ 0 := ProximityGap.KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom : Fin n ↪ ZMod p :=
    ProximityGap.KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g n (k - 1) =
      (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    dsimp only [dom]
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
        g hg hg0 (k - 1))
  have hcount : epsMCA (F := ZMod p) (A := ZMod p)
      (evalCode g n (k - 1)) (halfPredecessorRadius n) ≤
        (n : ℝ≥0∞) / (p : ℝ≥0∞) := by
    rw [hcode]
    simpa only [ZMod.card] using
      (epsMCA_halfPredecessor_rateEighth_le
        dom hn hh (by omega : 1 ≤ k) hrate)
  have hnormalized : (n : ℝ≥0∞) / (p : ℝ≥0∞) ≤
      ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) := by
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact (Fact.out (p := p.Prime)).ne_zero
    rw [ENNReal.div_le_iff hp0 (ENNReal.natCast_ne_top _)]
    have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      omega
    have hQtop : (Q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top Q
    calc
      (n : ℝ≥0∞) = (n : ℝ≥0∞) * Q * (Q : ℝ≥0∞)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hQ0 hQtop, mul_one]
      _ ≤ (p : ℝ≥0∞) * (Q : ℝ≥0∞)⁻¹ := by
        gcongr
        exact_mod_cast (show n * Q ≤ p by
          have hmul := Nat.mul_div_le p Q
          simpa [hfloor, Nat.mul_comm] using hmul)
      _ = (Q : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞) := mul_comm _ _
  have hlower : (1 / 2 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) :=
    half_le_mcaDeltaStar_of_predecessor_good hnEven (by omega)
      (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞)
      (hcount.trans hnormalized)
  have hkquarter : k ≤ n / 4 := by omega
  have hupper : mcaDeltaStar (F := ZMod p) (A := ZMod p)
      (evalCode g n (k - 1)) ((Q : ℝ≥0∞)⁻¹ : ℝ≥0∞) ≤
        (1 / 2 : ℝ≥0) :=
    mcaDeltaStar_le_half_of_floor_eq_length
      hg hQ hk hnEven hfloor hkquarter hsupply
  exact le_antisymm hupper hlower

end ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin.epsMCA_halfPredecessor_rateEighth_le
#print axioms
  ArkLib.ProximityGap.Frontier.HalfPredecessorRateEighthPin.evalCode_mcaDeltaStar_eq_half_of_rateEighth
