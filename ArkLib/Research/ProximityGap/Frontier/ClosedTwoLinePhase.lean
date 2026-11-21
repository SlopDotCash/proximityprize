/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ClosedManyLinePhase
import ArkLib.Research.ProximityGap.Frontier.UniversalTwoHeadBudget

/-! # The closed two-line phase on arbitrary sequences of finite fields

At equality in the cubic moment or core geometry test, every fixed smaller
radius still has a strict counting margin. At equality in the packing test,
every fixed larger radius still admits the over-budget two-head construction.
The resulting limits permit arbitrary variation of the finite parameters.
-/
set_option autoImplicit false
namespace ProximityGap.ClosedTwoLinePhase
open Filter Topology MCAThresholdLedger GeneralTwoLineArithmetic
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

variable (F : ℕ → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (n k : ℕ → ℕ) [∀ i, NeZero (n i)] (x : ∀ i, Fin (n i) ↪ F i) (Q : ℕ)

/-- Strictly beyond both the packing boundary and half-budget, the two-head
construction bounds the radius on every injective domain. -/
theorem eventually_failing (two : 2≤Q) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (hb : 0≤b) (core : ρ+b<1) (pack : 1<ρ+2*b) (budget : slope/Q < 2*b) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=F i)
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)) ≤
      ((⌊b*(n i:ℝ)⌋₊:ℕ):ℝ≥0)/n i := by
  let e i := ⌊b*(n i:ℝ)⌋₊
  have err := SmoothLinearFieldEnvelope.floor_fraction n hn hb
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have size := (rate.add err).eventually_lt_const core
  have deg := tiny.eventually_lt rate positive
  have enough := (rate.add (err.const_mul 2)).eventually_const_lt pack
  have allowed := (LinearFieldBudgetLimit.floor_limit (fun i => Fintype.card (F i)) n Q (by omega) hn hf).eventually_lt
    (err.const_mul 2) budget
  filter_upwards [size,deg,enough,allowed] with i cap ki haveRoom excess
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change (k i:ℝ)/n i+(e i:ℝ)/n i<1 at cap
  rw [←add_div,div_lt_one ni] at cap
  have fit : k i+e i < n i := by exact_mod_cast cap
  change 1/(n i:ℝ)<(k i:ℝ)/n i at ki
  have hk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp ki
  change 1 < (k i:ℝ)/n i+2*((e i:ℝ)/n i) at haveRoom
  rw [←mul_div_assoc,←add_div,one_lt_div ni] at haveRoom
  have room : n i ≤ k i+2*e i := by exact_mod_cast haveRoom.le
  change ((Fintype.card (F i)/Q:ℕ):ℝ)/n i < 2*((e i:ℝ)/n i) at excess
  rw [←mul_div_assoc,div_lt_div_iff_of_pos_right ni] at excess
  have ex : Fintype.card (F i)/Q < 2*e i := by exact_mod_cast excess
  simpa only [Fintype.card_fin] using UniversalTwoHeadBudget.ceiling (e:=e i) (x i) hk two
    (by rwa [Fintype.card_fin]) (by rw [Fintype.card_fin];omega) (by omega)

/-- Half the normalized budget is the limiting radius even at equality in
the packing, cubic-moment, or core-geometry inequality. -/
theorem limit (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : 2*a=slope/Q) (ha : 0<a) (core : ρ+a<1) (packing : 1≤ρ+2*a)
    (moment : ρ≤(1-a)^3) (geometry : 1+3*ρ≤3*(1-a)) :
    Tendsto (fun i => (mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro s hs
    apply ClosedManyLinePhase.eventually_above F n k x Q 2 (by decide) (by omega) hn hf rate positive
      (by simpa using index) ha core moment (by simpa using geometry) hs
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (lt_min hs (show a<1-ρ by linarith))
    have bp := ha.trans lb
    have bad := eventually_failing F n k x Q two hn hf rate positive bp.le
      (by have := ub.trans_le (min_le_right _ _);linarith) (by linarith) (by linarith)
    have strict := (SmoothLinearFieldEnvelope.floor_fraction n hn bp.le).eventually_lt_const
      (ub.trans_le (min_le_left _ _))
    filter_upwards [bad,strict] with i hi lt
    exact lt_of_le_of_lt (by exact_mod_cast hi) lt

/-- At the prize rate one eighth, normalized scalar budgets from seven
eighths through one give half their value as the limiting radius. -/
theorem rate_eighth (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope : ℝ}
    (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 (1/8)))
    (lower : 7/8 ≤ slope/Q) (upper : slope/Q≤1) :
    Tendsto (fun i => (mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 (slope/Q/2)) := by
  apply limit F n k x Q two hn hf rate (by norm_num) (by ring)
    (by linarith) (by linarith) (by linarith) _ (by linarith)
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) (show 1/2 ≤ 1-slope/Q/2 by linarith) 3
  norm_num at h ⊢
  linarith

end ProximityGap.ClosedTwoLinePhase
#print axioms ProximityGap.ClosedTwoLinePhase.eventually_failing
#print axioms ProximityGap.ClosedTwoLinePhase.limit
#print axioms ProximityGap.ClosedTwoLinePhase.rate_eighth
