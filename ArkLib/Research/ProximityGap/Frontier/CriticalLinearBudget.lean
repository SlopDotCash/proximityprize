/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LinearFieldBudgetLimit

/-! # Exact limiting threshold at the linear-field transition

Use a predecessor a fixed number of errors below the smaller of the spike
budget and the half-distance index. The integer gap in the apolar product
criterion stays bounded below, even when the normalized parameters approach
the transition from alternating sides.
-/

set_option autoImplicit false
namespace ProximityGap.CriticalLinearBudget
open Filter Topology LinearFieldBudgetRadius MCAThresholdLedger
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- If L extra sites are available below half distance, the factor 2L+3
in the apolar count suffices for any smaller budget test. -/
theorem good_index (x : Fin n ↪ F) {k Q a L : ℕ} (hk : 1≤k) (hQ : 0<Q)
    (ha : 1≤a) (budget : a≤Fintype.card F/Q) (room : k+2*(a+L)≤n)
    (cross : n<a*(2*L+3)) :
    (a:ℝ≥0)/n ≤ mcaDeltaStar (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (1/(Q:ℝ≥0∞)) := by
  apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good ha (by omega : a≤n)
  apply (upper x (e:=a-1) hk (by omega) (by omega) ?_).trans
  · rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ]
    omega
  · rw [show a-1+1=a by omega]
    exact cross.trans_le (Nat.mul_le_mul_left _ (by omega))

/-- The spike at the integer budget is bad whenever k+B+1 sites fit. -/
theorem spike_ceiling (x : Fin n ↪ F) {k Q B : ℕ} (hQ : 0<Q) (hB : B=Fintype.card F/Q)
    (hfit : B+1+k≤n) :
    mcaDeltaStar (F:=F) (ReedSolomon.code x k : Set (Fin n → F)) (1/(Q:ℝ≥0∞)) ≤ (B:ℝ≥0)/n := by
  apply mcaDeltaStar_le_of_bad _ _
  apply lt_of_lt_of_le _ (spike x hfit)
  apply lt_of_not_ge
  rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ,← hB]
  omega

/-- Limit of the integer predecessor used in the apolar lower bound. -/
theorem shifted_min_limit (p n k : ℕ → ℕ) [∀ i, NeZero (n i)] (Q L : ℕ)
    (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ : ℝ} (hρ : ρ<1)
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hγ : 0< min (slope/Q) ((1-ρ)/2)) :
    Tendsto (fun i => ((min (p i/Q) ((n i-k i)/2)-L : ℕ):ℝ)/n i) atTop
      (𝓝 (min (slope/Q) ((1-ρ)/2))) := by
  let a i := min (p i/Q) ((n i-k i)/2)
  let γ := min (slope/Q) ((1-ρ)/2)
  have half := rate.eventually_lt_const hρ
  have diff : Tendsto (fun i => ((n i-k i:ℕ):ℝ)/n i) atTop (𝓝 (1-ρ)) := by
    apply ((tendsto_const_nhds (x:=(1:ℝ))).sub rate).congr'
    filter_upwards [half] with i hi
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    have kl : k i≤n i := by exact_mod_cast (show (k i:ℝ)<n i by simpa using (div_lt_iff₀ ni).mp hi).le
    rw [Nat.cast_sub kl,sub_div,div_self ni.ne']
  have hmin := (LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf).min
    (LinearFieldBudgetLimit.floor_limit (fun i => n i-k i) n 2 (by decide) hn diff)
  have lim : Tendsto (fun i => ((a i:ℕ):ℝ)/n i) atTop (𝓝 γ) := hmin.congr fun i => by
    change min _ _ = ((min _ _:ℕ):ℝ)/_
    rw [Nat.cast_min,min_div_div_right (Nat.cast_nonneg _)]
  have tol := (tendsto_const_div_atTop_nhds_zero_nat (𝕜:=ℝ) (L:ℝ)).comp hn
  have total := lim.sub tol
  rw [sub_zero] at total
  refine total.congr' ?_
  filter_upwards [(lim.sub tol).eventually_const_lt (show (0:ℝ)<γ-0 by rw [sub_zero];exact hγ)] with i hi
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 0<(a i:ℝ)/n i-(L:ℝ)/n i at hi
  have lt := (div_lt_div_iff_of_pos_right ni).mp (sub_pos.mp hi)
  have le : L≤a i := by exact_mod_cast lt.le
  change _ = ((a i-L:ℕ):ℝ)/n i
  rw [Nat.cast_sub le,sub_div]
  rfl

/-- Fixed-step lower approximation on either side of the transition. -/
theorem eventually_good_index (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q L : ℕ) (hQ : 0<Q)
    (hk : ∀ᶠ i in atTop, 1≤k i) (hn : Tendsto n atTop atTop) {slope ρ : ℝ} (hρ : ρ<1)
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (margin : 1/(2*(L:ℝ)+3)< min (slope/Q) ((1-ρ)/2)) :
    ∀ᶠ i in atTop, ((min (p i/Q) ((n i-k i)/2)-L : ℕ):ℝ≥0)/n i ≤
      mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i)))
        (1/(Q:ℝ≥0∞)) := by
  let a i := min (p i/Q) ((n i-k i)/2)-L
  have den : (0:ℝ)<2*(L:ℝ)+3 := by positivity
  have lim := shifted_min_limit p n k Q L hQ hn hρ hf rate ((one_div_pos.mpr den).trans margin)
  filter_upwards [lim.eventually_const_lt margin,hk,rate.eventually_lt_const hρ] with i h hk hρi
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1/(2*(L:ℝ)+3)<(a i:ℝ)/n i at h
  have bound : n i<a i*(2*L+3) := by
    have := (div_lt_div_iff₀ den ni).mp h
    exact_mod_cast (by simpa using this : (n i:ℝ)<a i*(2*(L:ℝ)+3))
  have kl : k i<n i := by exact_mod_cast (show (k i:ℝ)<n i by simpa using (div_lt_iff₀ ni).mp hρi)
  have ha : 0<a i := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz,zero_mul] at bound
    omega
  have hb := min_le_left (p i/Q) ((n i-k i)/2)
  have hh := min_le_right (p i/Q) ((n i-k i)/2)
  dsimp [a] at ha bound
  apply good_index (L:=L) (x i) hk hQ ha (by rw [ZMod.card];omega) (by omega) bound

/-- At equality the normalized threshold converges even if the finite
parameters cross the half-distance boundary infinitely often. -/
theorem critical_limit (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ) (hQ : 0<Q)
    (hk : ∀ᶠ i in atTop, 1≤k i) (hn : Tendsto n atTop atTop)
    {slope ρ : ℝ} (hρ : ρ<1)
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (critical : ρ+2*(slope/Q)=1) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) : ℝ))
      atTop (𝓝 (slope/Q)) := by
  have bpos : 0 < slope/(Q:ℝ) := by linarith
  have heq : min (slope/(Q:ℝ)) ((1-ρ)/2) = slope/Q := by apply min_eq_left;linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (1/(slope/(Q:ℝ)))
  have hlarge : 1/(2*(L:ℝ)+3)< min (slope/Q) ((1-ρ)/2) := by
    rw [heq,div_lt_iff₀ (by positivity)]
    have h := (div_lt_iff₀ bpos).mp hL
    nlinarith
  have lo := eventually_good_index p n k x Q L hQ hk hn hρ hf rate hlarge
  have ll := shifted_min_limit p n k Q L hQ hn hρ hf rate (heq.symm ▸ bpos)
  rw [heq] at ll
  have up := LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ll up
  · filter_upwards [lo] with i h
    exact_mod_cast h
  · have chk := (rate.add up).eventually_lt_const (show ρ+slope/Q<1 by linarith)
    filter_upwards [chk] with i hi
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    change (k i:ℝ)/n i + ((p i/Q:ℕ):ℝ)/n i < 1 at hi
    rw [← add_div,div_lt_iff₀ ni,one_mul] at hi
    have hfit : k i+p i/Q<n i := by exact_mod_cast hi
    exact_mod_cast spike_ceiling (x i) hQ (by simp : p i/Q=Fintype.card (ZMod (p i))/Q)
      (show p i/Q+1+k i≤n i by omega)

end ProximityGap.CriticalLinearBudget
#print axioms ProximityGap.CriticalLinearBudget.eventually_good_index
#print axioms ProximityGap.CriticalLinearBudget.critical_limit
