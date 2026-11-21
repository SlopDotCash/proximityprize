/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralManyLineSafety
import ArkLib.Research.ProximityGap.Frontier.GeneralTwoLineArithmetic
import ArkLib.Research.ProximityGap.Frontier.SmoothLinearFieldEnvelope

/-! # Closed many-line phase boundaries

The uniform finite cubic and core-geometry estimates imply a lower limiting
radius on arbitrary finite fields and evaluation domains. A matching upper
bound arbitrarily close to that radius pins the limit, even if either
incidence inequality is an equality at the threshold.
-/
set_option autoImplicit false
namespace ProximityGap.ClosedManyLinePhase
open Filter Topology MCAThresholdLedger GeneralTwoLineArithmetic CosetHeadSlopes
open scoped NNReal ENNReal
variable (F : ℕ → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (n k : ℕ → ℕ) [∀ i, NeZero (n i)] (x : ∀ i, Fin (n i) ↪ F i) (Q : ℕ)

/-- A strict cubic and core-geometry margin at a fixed relative error gives
eventual safety at its rounded-down error count if the error times the number of heads is below
the limiting budget. -/
theorem eventually_safe (r : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (hb : 0<b) (core : ρ+b<1) (moment : ρ<(1-b)^3) (geom : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-b))
    (budget : (r:ℝ)*b < slope/Q) :
    ∀ᶠ i in atTop, ((⌊b*(n i:ℝ)⌋₊:ℕ):ℝ≥0)/n i ≤ mcaDeltaStar (F:=F i)
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)) := by
  let e i := ⌊b*(n i:ℝ)⌋₊
  have err := SmoothLinearFieldEnvelope.floor_fraction n hn hb.le
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have size := (rate.add err).eventually_lt_const core
  have deg := tiny.eventually_lt rate positive
  have allowed := ((err.add tiny).const_mul (r:ℝ)).eventually_lt
    (LinearFieldBudgetLimit.floor_limit (fun i => Fintype.card (F i)) n Q hQ hn hf) (by simpa using budget)
  obtain ⟨L,hL,conds⟩ := eventually_many_line_hypotheses r n k e hn hb (by linarith) err rate moment geom
  filter_upwards [size,deg,allowed,conds] with i cap ki budget_i h
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change (k i:ℝ)/n i+(e i:ℝ)/n i<1 at cap
  rw [←add_div,div_lt_one ni] at cap
  have room : k i+e i ≤ n i := by exact_mod_cast cap.le
  change 1/(n i:ℝ)<(k i:ℝ)/n i at ki
  have hk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp ki
  change (r:ℝ)*((e i:ℝ)/n i+1/n i)<((Fintype.card (F i)/Q:ℕ):ℝ)/n i at budget_i
  rw [←add_div,←mul_div_assoc,div_lt_div_iff_of_pos_right ni] at budget_i
  have count : r*(e i+1)≤Fintype.card (F i)/Q := by exact_mod_cast budget_i.le
  have bound := GeneralManyLineSafety.epsMCA_le (x i) ((e i:ℝ≥0)/n i) (Fintype.card_fin _)
    (show e i+(n i-e i)=n i by omega) (by omega : 1≤k i) (show k i ≤ n i-e i by omega)
    hL hr (by rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),
      ←Nat.cast_tsub,Nat.ceil_natCast]) h.2.1 h.2.2
  apply le_mcaDeltaStar_of_good _ _
  · exact (div_le_one (by exact_mod_cast NeZero.pos (n i) : (0:ℝ≥0)<n i)).mpr (by exact_mod_cast h.1)
  · exact bound.trans ((BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ).2 count)

/-- Below the closed moment and core-geometry boundaries the operational
radius eventually exceeds every fixed real number below half-budget for two
heads, or the corresponding rth share of the budget for r heads. -/
theorem eventually_above (r : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : (r:ℝ)*a=slope/Q) (ha : 0<a) (core : ρ+a<1)
    (moment : ρ≤(1-a)^3) (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ ≤ ((r+1:ℕ):ℝ)*(1-a))
    {s : ℝ} (hs : s<a) : ∀ᶠ i in atTop, s < (mcaDeltaStar (F:=F i)
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)):ℝ) := by
  obtain ⟨b,lb,ub⟩ := exists_between (max_lt hs ha)
  have bp : 0<b := (le_max_right _ _).trans_lt lb
  have rp : (0:ℝ)<r := by exact_mod_cast hr
  have cube : (1-a)^3 < (1-b)^3 := pow_lt_pow_left₀ (by linarith) (by linarith) (by decide)
  have wider := mul_lt_mul_of_pos_left (show 1-a<1-b by linarith) (show (0:ℝ)<(r+1:ℕ) by positivity)
  have good := eventually_safe F n k x Q r hr hQ hn hf rate positive bp (by linarith)
    (moment.trans_lt cube) (geometry.trans_lt wider) (index ▸ (mul_lt_mul_of_pos_left ub rp))
  have strict := (SmoothLinearFieldEnvelope.floor_fraction n hn bp.le).eventually_const_lt
    ((le_max_left _ _).trans_lt lb)
  filter_upwards [good,strict] with i lo lt
  exact lt.trans_le (by exact_mod_cast lo)

/-- On smooth prime-field domains, the limiting radius is the rth share
of the budget throughout the closed packing, cubic and geometry range. -/
theorem smooth_limit (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (d Q : ℕ) (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : ((d+1:ℕ):ℝ)*a=slope/Q) (ha : 0<a) (core : ρ+a<1)
    (packing : ((d+1:ℕ):ℝ)*(1-ρ-a) ≤ 1-ρ) (moment : ρ≤(1-a)^3)
    (geometry : 1+(((d+1).choose 2+(d+1):ℕ):ℝ)*ρ ≤ ((d+2:ℕ):ℝ)*(1-a))
    (supply : (((edges (d+2)).offDiag.card*(d+1):ℕ):ℝ)<slope) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro s hs
    exact eventually_above _ n k x Q (d+1) (by omega) hQ hn (by simpa only [ZMod.card] using hf)
      rate positive index ha core moment geometry hs
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (lt_min hs (show a<1-ρ by linarith))
    have rp : (0:ℝ)<(d+1:ℕ) := by positivity
    have less := mul_lt_mul_of_pos_left (show 1-ρ-b<1-ρ-a by linarith) rp
    have upper := SmoothLinearFieldEnvelope.eventually_at_most p n k x d Q hQ hn hf rate positive
      (ha.trans lb).le (by have := ub.trans_le (min_le_right _ _);linarith)
      (less.trans_le packing) supply (index ▸ mul_lt_mul_of_pos_left lb rp)
    filter_upwards [upper] with i hi
    exact hi.trans_lt (ub.trans_le (min_le_left _ _))

end ProximityGap.ClosedManyLinePhase
#print axioms ProximityGap.ClosedManyLinePhase.eventually_safe
#print axioms ProximityGap.ClosedManyLinePhase.eventually_above
#print axioms ProximityGap.ClosedManyLinePhase.smooth_limit
