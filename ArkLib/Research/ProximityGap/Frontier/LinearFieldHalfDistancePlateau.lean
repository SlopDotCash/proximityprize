/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget

/-! # A half-distance plateau for line MCA on arbitrary prime-field domains

The apolar predecessor and a two-head witness give matching limiting radii
throughout the entire interval from half to full relative redundancy in
the normalized scalar budget.
-/
set_option autoImplicit false
namespace ProximityGap.LinearFieldHalfDistancePlateau
open Filter Topology MCAThresholdLedger CriticalLinearBudget
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

private theorem upper_index_limit (p n k : ℕ → ℕ) [∀ i, NeZero (n i)] (Q : ℕ)
    (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ : ℝ} (hρ : ρ<1)
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    Tendsto (fun i => ((max ((n i-k i+1)/2) (p i/Q/2):ℕ):ℝ)/n i) atTop
      (𝓝 (max ((1-ρ)/2) (slope/Q/2))) := by
  have kl := rate.eventually_lt_const hρ
  have below : Tendsto (fun i => ((n i-k i+1:ℕ):ℝ)/n i) atTop (𝓝 (1-ρ)) := by
    have q := ((tendsto_const_nhds (x:=(1:ℝ))).sub rate).add
      ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
    rw [add_zero] at q
    apply q.congr'
    filter_upwards [kl] with i hi
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    have le : k i≤n i := by exact_mod_cast (show (k i:ℝ)<n i by simpa using (div_lt_iff₀ ni).mp hi).le
    simp only [Nat.cast_add_one,Nat.cast_sub le,add_div,sub_div,div_self ni.ne']
    rfl
  have low := LinearFieldBudgetLimit.floor_limit (fun i => n i-k i+1) n 2 (by decide) hn below
  have high := LinearFieldBudgetLimit.floor_limit (fun i => p i/Q) n 2 (by decide) hn
    (LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf)
  refine (low.max high).congr fun i => ?_
  change max _ _ = ((max _ _:ℕ):ℝ)/_
  rw [Nat.cast_max,max_div_div_right (Nat.cast_nonneg _)]

/-- If the limiting scalar budget is between half and all of the redundancy,
the operational threshold tends to half the redundancy on every prescribed
domain. Both endpoints of the interval are included. -/
theorem plateau (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ) (hQ : 0<Q)
    (hn : Tendsto n atTop atTop) {slope ρ : ℝ} (hρ₀ : 0<ρ) (hρ₁ : ρ<1)
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (left : (1-ρ)/2≤ slope/Q) (right : slope/Q≤1-ρ) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) : ℝ))
      atTop (𝓝 ((1-ρ)/2)) := by
  let h := (1-ρ)/2
  have hpos : 0<h := by dsimp [h];linarith
  have hmin : min (slope/Q) ((1-ρ)/2) = h := min_eq_right left
  have hmax : max ((1-ρ)/2) (slope/Q/2) = h := max_eq_left (by linarith)
  obtain ⟨L,hL⟩ := exists_nat_gt (1/h)
  have margin : 1/(2*(L:ℝ)+3)< min (slope/Q) ((1-ρ)/2) := by
    rw [hmin,div_lt_iff₀ (by positivity)]
    have b := (div_lt_iff₀ hpos).mp hL
    nlinarith
  have hk : ∀ᶠ i in atTop, 1≤k i := by
    filter_upwards [rate.eventually_const_lt hρ₀] with i hi
    by_contra! h
    simp [show k i=0 by omega] at hi
  have lo := eventually_good_index p n k x Q L hQ hk hn hρ₁ hf rate margin
  have ll := shifted_min_limit p n k Q L hQ hn hρ₁ hf rate (by rw [hmin];exact hpos)
  have ul := upper_index_limit p n k Q hQ hn hρ₁ hf rate
  rw [hmin] at ll
  rw [hmax] at ul
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ll ul
  · filter_upwards [lo] with i hi
    exact_mod_cast hi
  · let e i := max ((n i-k i+1)/2) (p i/Q/2)
    have ur := ul.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
    rw [add_zero] at ur
    have pair := (ur.add ur).eventually_lt_const (show h+h<1 by dsimp [h];linarith)
    have core := (rate.add ur).eventually_lt_const (show ρ+h<1 by dsimp [h];linarith)
    filter_upwards [pair,core] with i pair core
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    change ((e i:ℝ)/n i+1/n i)+((e i:ℝ)/n i+1/n i)<1 at pair
    change (k i:ℝ)/n i+((e i:ℝ)/n i+1/n i)<1 at core
    simp only [← add_div,div_lt_one ni] at pair core
    have pr : 2*(e i+1)≤Fintype.card (Fin (n i)) := by
      rw [Fintype.card_fin]
      exact_mod_cast (show 2*((e i:ℝ)+1)≤n i by linarith)
    have cr : k i+e i+1≤Fintype.card (Fin (n i)) := by
      rw [Fintype.card_fin]
      exact_mod_cast (show (k i:ℝ)+e i+1≤n i by linarith)
    have l := le_max_left ((n i-k i+1)/2) (p i/Q/2)
    have b := le_max_right ((n i-k i+1)/2) (p i/Q/2)
    have dr : Fintype.card (Fin (n i))≤k i+2*e i := by rw [Fintype.card_fin];dsimp [e];omega
    have fail := TwoHeadLinearBudget.errors (x i) pr dr cr
    rw [Fintype.card_fin,ZMod.card] at fail
    have exceed : (1/(Q:ℝ≥0∞)) < ((2*(e i+1):ℕ):ℝ≥0∞)/(p i) := by
      apply lt_of_not_ge
      rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=(p i).Prime)).pos hQ]
      dsimp [e];omega
    exact_mod_cast mcaDeltaStar_le_of_bad _ _ (exceed.trans_le fail)

end ProximityGap.LinearFieldHalfDistancePlateau
#print axioms ProximityGap.LinearFieldHalfDistancePlateau.plateau
