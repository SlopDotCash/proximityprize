/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ArkLib.Research.ProximityGap.Frontier.ApolarMovingCount
import ArkLib.Research.ProximityGap.Frontier.FourRatePairBudget

/-! # The exact spike range from the apolar count

The argument applies to every smooth prime-field domain of the production
length. It determines all four official rates for every budget strictly below
one quarter of the length, and each rate below one third through the entire
unique-decoding plateau.
-/

set_option autoImplicit false
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open ArkLib.ProximityGap.Frontier.FourRatePairBudget (n code)
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.Frontier.ApolarSpikeBudgetRange

/-- The product criterion certifies at most e+1 bad scalars for every pair. -/
theorem count_upper {p k e : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hroom : k+2*e ≤ n) (hfit : k+e < n)
    (hgap : n < (e+1)*(n-k+1-2*e)) :
    epsMCA (F := ZMod p) (code g k) ((e:ℝ≥0)/n) ≤ ((e+1 : ℕ):ℝ≥0∞)/(p:ℝ≥0∞) := by
  classical
  let dom := KKH26RegimeSplit.powDomain g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg)
  let δ : ℝ≥0 := (e:ℝ≥0)/n
  let d := n-k-1
  have hcode : code g k = (ReedSolomon.code dom k : Set (Fin n → ZMod p)) := by
    simpa only [code,dom,show k-1+1 = k by omega] using
      KKH26RegimeSplit.evalCode_eq_reedSolomon g hg (KKH26RegimeSplit.ne_zero_of_orderOf_eq hg) (k-1)
  rw [hcode]
  apply (epsMCA_le_of_badCount_le _ _ (e+1) ?_).trans (by rw [ZMod.card])
  intro u
  let fam := canonicalBadScalarRichPointFamily dom δ u hk
  change fam.G.card ≤ e+1
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin _
  have h := _root_.ProximityGap.ApolarMovingCount.count_mca_family
    (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) fam fam.G (Finset.Subset.rfl)
    (e:=e) (d:=d) (by dsimp [d];omega) (by dsimp [d];omega) hk
    (by rw [hcard];dsimp [d];omega) (by
      rw [show ⌈(1-δ)*(Fintype.card (Fin n):ℝ≥0)⌉₊ = n-e from
        TwoCorePackingThreshold.agreement_ceiling e (show e ≤ n by omega),hcard])
  rcases h with h | h
  · exact h
  · by_contra! ht
    apply hgap.not_ge
    rw [hcard,show d+2-2*e = n-k+1-2*e by dsimp [d];omega] at h
    exact (Nat.mul_le_mul_right _ (by omega : e+1 ≤ fam.G.card-1)).trans h

private theorem spike {p k e : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hroom : e+1+k ≤ n) :
    ((e+1 : ℕ):ℝ≥0∞)/(p:ℝ≥0∞) ≤ epsMCA (F := ZMod p) (code g k) ((e:ℝ≥0)/n) := by
  let dom := Ownership.smoothDom g n hg
  let pos : Fin (e+1) ↪ Fin n := Fin.castLEEmb (by omega)
  rw [code,Ownership.evalCode_pred_eq_rsCode hg hk]
  conv_lhs => rw [← ZMod.card p]
  exact SpikeFloor.epsMCA_ge_j_div_card (SpikeFloor.rsCode dom k)
    (SpikeFloor.rsCode_noWeightLE dom hroom) (by simp [Fintype.card_fin,n]) (by omega)
    (by rw [Fintype.card_fin];omega) pos (pos.trans dom) (b := (1:ZMod p)) one_ne_zero

private theorem budget_lt_mass {p a : ℕ} [Fact p.Prime] (h : p/2^128 < a) :
    (epsStar:ℝ≥0∞) < (a:ℝ≥0∞)/(p:ℝ≥0∞) := by
  rw [epsStar_coe_eq_natCast_inv]
  have hp : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out (p:=p.Prime)).ne_zero
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl (ENNReal.natCast_ne_top p)),
    ← ENNReal.div_eq_inv_mul,ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (ENNReal.natCast_ne_top _))]
  have hn := (Nat.lt_mul_div_succ p (by decide : 0<2^128)).trans_le (Nat.mul_le_mul_left _ h)
  exact_mod_cast (by simpa only [Nat.mul_comm] using hn)

private theorem predecessor_safe {p k j : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hroom : k+2*j ≤ n)
    (hgap : n < j*(n-k+3-2*j)) (hb : j ≤ p/2^128) :
    epsMCA (F := ZMod p) (code g k) (((j-1:ℕ):ℝ≥0)/n) ≤ (epsStar:ℝ≥0∞) := by
  have hu := count_upper (e:=j-1) hg hk (by omega) (by omega) (by
    rwa [Nat.sub_add_cancel hj,show n-k+1-2*(j-1) = n-k+3-2*j by omega])
  rw [Nat.sub_add_cancel hj] at hu
  rw [epsStar_coe_eq_natCast_inv]
  exact hu.trans (natCast_div_le_inv_of_mul_le (Q:=2^128) (by decide) (Fact.out (p:=p.Prime)).pos
    ((Nat.mul_le_mul_right _ hb).trans (Nat.div_mul_le_self ..)))

/-- A prime-field budget below a quarter of the block length is the exact
first bad Hamming count at every dimension through rate one half. -/
theorem four_rate_budget {p k B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 1 ≤ k) (hmax : k ≤ 536870912) (hB : B = p/2^128) (hpos : 1 ≤ B)
    (hlim : B ≤ 268435455) :
    mcaDeltaStar (F := ZMod p) (code g k) (epsStar:ℝ≥0∞) = (B:ℝ≥0)/n := by
  by_cases hold : B ≤ FourRatePairBudget.upperBudget
  · exact FourRatePairBudget.threshold hg hk hmax hB hpos hold
  have hbig : 181823221 < B := by simpa only [FourRatePairBudget.upperBudget,not_le] using hold
  have hroom : k+2*B ≤ n := by dsimp [n];omega
  have hgap : n < B*(n-k+3-2*B) := by
    by_cases s : 6 ≤ n-k+3-2*B
    · exact (by dsimp [n];omega : n < B*6).trans_le (Nat.mul_le_mul_left B s)
    · have b : B=268435455 := by dsimp [n] at s;omega
      have ss : 5 ≤ n-k+3-2*B := by dsimp [n];omega
      exact (by rw [b];decide : n < B*5).trans_le (Nat.mul_le_mul_left B ss)
  apply le_antisymm (mcaDeltaStar_le_of_bad _ _ ((budget_lt_mass (by omega : p/2^128 < B+1)).trans_le
    (spike hg hk (by omega))))
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good hpos (by omega : B≤n)
  exact predecessor_safe hg hk hpos hroom hgap hB.le

private theorem interior_product {j a : ℕ} (hlo : 2 ≤ j) (hhi : j ≤ a) (hh : n < 3*a) :
    n < j*(2*a+3-2*j) := by
  zify [show 2*j ≤ 2*a+3 by omega] at *
  nlinarith [mul_nonneg (show (0:ℤ) ≤ (j:ℤ)-2 by omega) (show (0:ℤ) ≤ (a:ℤ)-j by omega)]

/-- Through the bisimplex endpoint every lower-rate threshold is the smaller
of the field budget and the first unique-decoding boundary. -/
theorem lower_rate_budget {p k a B : ℕ} [Fact p.Prime] {g : ZMod p} (hg : orderOf g = n)
    (hk : 2 ≤ k) (hka : k+2*a=n) (hthird : n<3*a) (hB : B=p/2^128)
    (hpos : 1≤B) (hlim : B≤2*a+1) :
    mcaDeltaStar (F := ZMod p) (code g k) (epsStar:ℝ≥0∞) = ((min B a:ℕ):ℝ≥0)/n := by
  have ha : 2 ≤ a := by dsimp [n] at *;omega
  have hdim : k ≤ 536870912 := by dsimp [n] at *;omega
  by_cases hone : B ≤ 1
  · rw [min_eq_left (by omega : B≤a)]
    exact four_rate_budget hg (by omega) hdim hB hpos (by omega)
  let j := min B a
  have hj : 2 ≤ j := le_min (by omega) ha
  have hja : j ≤ a := min_le_right ..
  have hb : j ≤ B := min_le_left ..
  have hroom : k+2*j ≤ n := by omega
  have hgap : n < j*(n-k+3-2*j) := by
    rw [show n-k = 2*a by omega]
    exact interior_product hj hja hthird
  change _ = (j:ℝ≥0)/n
  apply le_antisymm
  · by_cases small : B ≤ a
    · have hjb : j=B := min_eq_left small
      exact mcaDeltaStar_le_of_bad _ _ ((budget_lt_mass (by omega : p/2^128 < j+1)).trans_le
        (spike hg (by omega) (by omega)))
    · have hje : j=a := min_eq_right (by omega)
      rw [hje]
      have mass := BadFamilyCensus.mcaDeltaStar_le_bisimplex (d:=k-1) (e:=a) hg (by omega)
        (by omega) (by omega) (by omega) (epsStar:ℝ≥0∞) (budget_lt_mass (by omega))
      have hn : (n:ℝ≥0) ≠ 0 := by norm_num [n]
      have has : (a:ℝ≥0)/n ≤ 1 := (div_le_one (pos_iff_ne_zero.mpr hn)).2 (by exact_mod_cast (by omega : a≤n))
      rwa [Nat.cast_tsub,tsub_div,div_self hn,tsub_tsub_cancel_of_le has] at mass
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good (by omega) (by omega : j≤n)
    exact predecessor_safe hg (by omega) (by omega) hroom hgap (by omega)

#print axioms four_rate_budget
#print axioms lower_rate_budget

end ArkLib.ProximityGap.Frontier.ApolarSpikeBudgetRange
