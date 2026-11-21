/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier._ShortenedDomainGoodSide
import ArkLib.Research.ProximityGap.Frontier._PackingBudgetFirstJump
import ArkLib.Research.ProximityGap.Frontier._ShorteningWindowPrime

/-!
# Exact MCA thresholds from shortening and overlap packing

At error count `N/2 - 1`, shortening bounds the number of bad scalars by `N`.
At error count `N/2`, overlap packing supplies `N+2` bad scalars. This identifies
the first bad Hamming step whenever the integer budget is `N` or `N+1`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.Frontier.ShortenedDomainPackingPin

open PrizeShapeRateHalfBracket

/-- Strict failure of the target error at the packing step. -/
theorem bad_at_packing_step {p n k e Q : ℕ} [Fact p.Prime] [NeZero n]
    {g : ZMod p} (hg : orderOf g = n) (hQ : 0 < Q) (hk : 2 ≤ k)
    (hehalf : n ≤ 2 * e) (hecap : e + k + 1 ≤ n)
    (hsupply : 2 * (2 * e - n + 2) ≤ p - n) (hbudget : p / Q ≤ 2 * e + 1) :
    (Q : ℝ≥0∞)⁻¹ < epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
      ((e : ℝ≥0) / (n : ℝ≥0)) := by
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  have hmul : p < Q * (2 * e + 2) :=
    (Nat.lt_mul_div_succ p hQ).trans_le (Nat.mul_le_mul_left Q (by omega))
  have hstrict : (Q : ℝ≥0∞)⁻¹ < ((2 * e + 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
    have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
    have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQ.ne'
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp0) (Or.inl (ENNReal.natCast_ne_top p)),
      ← ENNReal.div_eq_inv_mul,
      ENNReal.div_lt_iff (Or.inl hQ0) (Or.inl (ENNReal.natCast_ne_top Q))]
    exact_mod_cast (by simpa only [Nat.mul_comm] using hmul)
  have hpack := PackingBudgetFirstJump.overlap_epsMCA_lower_bound_of_supply
    hg hk hehalf hecap hsupply
  have hn0 : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hfrac : (((n - e : ℕ) : ℝ≥0) / (n : ℝ≥0)) ≤ 1 := by
    apply (div_le_one (pos_iff_ne_zero.mpr hn0)).2
    exact_mod_cast Nat.sub_le n e
  have hsum : e + (n - e) = n := by omega
  have hradius : (1 : ℝ≥0) - (((n - e : ℕ) : ℝ≥0) / (n : ℝ≥0)) =
      (e : ℝ≥0) / (n : ℝ≥0) := by
    rw [tsub_eq_iff_eq_add_of_le hfrac, ← add_div, ← Nat.cast_add, hsum, div_self hn0]
  rw [hradius] at hpack
  exact hstrict.trans_le hpack

/-- The shortening lower bound only requires enough field budget to pay for the extended
length. It also applies when the overlap-packing jump occurs at a higher error count. -/
theorem shortening_threshold_lower {p n N k Q : ℕ} [Fact p.Prime] [NeZero n] [NeZero N]
    {g : ZMod p} (hg : orderOf g = n) (hn : n ≤ N) (hfield : N ≤ p)
    (heven : N = 2 * (N / 2)) (hlarge : 1699 ≤ N / 2) (ha : N / 2 ≤ n)
    (hQ : 0 < Q) (hk : 1 ≤ k) (hrate : 8 * (k + (N - n)) ≤ N) (hlo : N ≤ p / Q) :
    ((N / 2 : ℕ) : ℝ≥0) / (n : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1)) (Q : ℝ≥0∞)⁻¹ := by
  classical
  have hg0 := KKH26RegimeSplit.ne_zero_of_orderOf_eq hg
  let dom := KKH26RegimeSplit.powDomain g hg hg0
  have hcode : evalCode g n (k - 1) = (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [dom, show k - 1 + 1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg hg0 (k - 1)
  have hprev : epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1))
      (predecessorRadius n (N / 2)) ≤ (Q : ℝ≥0∞)⁻¹ := by
    rw [hcode]
    refine (epsMCA_le_of_badCount_le _ _ N fun u =>
      ShortenedDomainGoodSide.predecessor_badCount_le dom hn
        (by simpa only [ZMod.card] using hfield) heven hlarge ha hk
        hrate u).trans ?_
    rw [ZMod.card]
    apply natCast_div_le_inv_of_mul_le hQ (Fact.out (p := p.Prime)).pos
    calc
      N * Q ≤ (p / Q) * Q := Nat.mul_le_mul_right Q hlo
      _ ≤ p := Nat.div_mul_le_self p Q
  exact latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by omega) ha _ _ hprev

/-- The exact supremum for every smooth domain that can be extended to a rate-at-most-one-eighth
code at one of the two integer budgets around the packing jump. -/
theorem mcaDeltaStar_eq_packing_step {p n N k Q : ℕ} [Fact p.Prime] [NeZero n] [NeZero N]
    {g : ZMod p} (hg : orderOf g = n) (hn : n ≤ N) (hfield : N ≤ p)
    (heven : N = 2 * (N / 2)) (hlarge : 1699 ≤ N / 2) (hQ : 0 < Q) (hk : 2 ≤ k)
    (hrate : 8 * (k + (N - n)) ≤ N) (hlo : N ≤ p / Q)
    (hhi : p / Q ≤ N + 1) (hcap : p / Q ≤ 2 * (n - k) - 1)
    (hsupply : 2 * (N - n + 2) ≤ p - n) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (k - 1)) (Q : ℝ≥0∞)⁻¹ =
      ((N / 2 : ℕ) : ℝ≥0) / (n : ℝ≥0) := by
  classical
  have hecap : N / 2 + k + 1 ≤ n := by omega
  have hbad := bad_at_packing_step (e := N / 2) hg hQ hk (by omega) hecap
    (by omega) (by omega : p / Q ≤ 2 * (N / 2) + 1)
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ hbad)
  exact shortening_threshold_lower hg hn hfield heven hlarge (by omega) hQ (by omega) hrate hlo

/-- At the sponsor length, rate and target error, the window on the even budget supplies every
arithmetic hypothesis of the shortening and packing arguments. -/
theorem rateSixteenth_window {p : ℕ} [Fact p.Prime] {g : ZMod p}
    (hg : orderOf g = 2 ^ 30)
    (hlo : 2 ^ 30 ≤ 2 * ((p / 2 ^ 128) / 2))
    (hhi : 2 * ((p / 2 ^ 128) / 2) ≤ 2 ^ 30 + 2 ^ 30 / 14) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g (2 ^ 30) (2 ^ 26 - 1))
      (ProximityGap.epsStar : ℝ≥0∞) =
      (((p / 2 ^ 128) / 2 : ℕ) : ℝ≥0) / (2 ^ 30 : ℝ≥0) := by
  let B := p / 2 ^ 128
  let N := 2 * (B / 2)
  change 2 ^ 30 ≤ N at hlo
  change N ≤ 2 ^ 30 + 2 ^ 30 / 14 at hhi
  have hhalf : N / 2 = B / 2 := by dsimp only [N]; omega
  have hNEven : N = 2 * (N / 2) := by rw [hhalf]
  have hNB : N ≤ B := by dsimp only [N]; omega
  have hBN : B ≤ N + 1 := by dsimp only [N]; omega
  have hp : B * 2 ^ 128 ≤ p := Nat.div_mul_le_self _ _
  have hdouble : N * 2 ≤ p := le_trans
    (Nat.mul_le_mul hNB (by norm_num : 2 ≤ 2 ^ 128)) hp
  have hcap : B ≤ 2 * (2 ^ 30 - 2 ^ 26) - 1 := by omega
  have : NeZero N := ⟨by omega⟩
  rw [epsStar_coe_eq_natCast_inv]
  have h := mcaDeltaStar_eq_packing_step (Q := 2 ^ 128) (N := N) (k := 2 ^ 26)
    hg hlo (by omega) hNEven (by omega) (by norm_num) (by norm_num)
    (by omega) hNB hBN hcap (by omega)
  simpa only [hhalf, Nat.cast_pow, Nat.cast_ofNat] using h

/-- For the displayed prime, the rate-one-sixteenth code has supremum `16807/32768` at
the original target error `2^-128`. Its length is `2^30` and its dimension is `2^26`. -/
theorem shorteningWindowPrime_rateSixteenth_threshold :
    mcaDeltaStar (F := ZMod ShorteningWindowPrime.P) (A := ZMod ShorteningWindowPrime.P)
      (evalCode ShorteningWindowPrime.g (2 ^ 30) (2 ^ 26 - 1)) (ProximityGap.epsStar : ℝ≥0∞) =
      (16807 / 32768 : ℝ≥0) := by
  have h := rateSixteenth_window ShorteningWindowPrime.orderOf_g
    ShorteningWindowPrime.even_budget_window.1.le ShorteningWindowPrime.even_budget_window.2
  rw [ShorteningWindowPrime.P_div_two_pow_128] at h
  convert h using 1
  norm_num

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- The second repository prime has budget twice the original length. Taking the largest
even extension in the rate-one-sixteenth window raises its certified threshold floor. -/
theorem secondPrime_rateSixteenth_shortening_floor :
    (287609417 / 536870912 : ℝ≥0) ≤
      mcaDeltaStar (F := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (A := ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
        (evalCode ArkLib.ProximityGap.PrizeShapePrimeP30Second.g (2 ^ 30) (2 ^ 26 - 1))
        (ProximityGap.epsStar : ℝ≥0∞) := by
  have : NeZero (1150437668 : ℕ) := ⟨by norm_num⟩
  rw [epsStar_coe_eq_natCast_inv]
  have h := shortening_threshold_lower (N := 1150437668) (k := 2 ^ 26) (Q := 2 ^ 128)
    ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
    (by norm_num) (by norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P_div_two_pow_128]; norm_num)
  convert h using 1
  norm_num

#print axioms secondPrime_rateSixteenth_shortening_floor
#print axioms shortening_threshold_lower
#print axioms bad_at_packing_step
#print axioms mcaDeltaStar_eq_packing_step
#print axioms rateSixteenth_window
#print axioms shorteningWindowPrime_rateSixteenth_threshold

end ArkLib.ProximityGap.Frontier.ShortenedDomainPackingPin
