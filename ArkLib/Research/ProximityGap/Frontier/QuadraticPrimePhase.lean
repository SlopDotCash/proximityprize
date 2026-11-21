/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.QuadraticTwoHeadThreshold
import ArkLib.Research.ProximityGap.Frontier.ClosedTwoLinePhase

/-! # The limiting two-head threshold from a quadratic interpolant

The finite degree-34 estimate gives a closed linear agreement condition.
In prime fields this extends the limiting rate-one-eighth classification
past normalized budget one on arbitrary sequences of evaluation domains.
-/
set_option autoImplicit false
namespace ProximityGap.QuadraticPrimePhase
open Filter Topology MCAThresholdLedger QuadraticTwoHeadThreshold
open scoped NNReal ENNReal

variable (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ)

/-- At any strictly smaller radius all three finite tests have a margin:
the interpolation surplus, the characteristic, and the integer budget. -/
theorem eventually_safe (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ b : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hρ : 0<ρ) (cap : 3*ρ<1) (hb : 0<b) (bn : b<1)
    (surplus : 35+100*ρ<102*(1-b)) (characteristic : 70+200*ρ<102*slope)
    (budget : 2*b<slope/Q) :
    ∀ᶠ i in atTop, ((⌊b*(n i:ℝ)⌋₊:ℕ):ℝ≥0)/n i ≤ mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) := by
  let e i := ⌊b*(n i:ℝ)⌋₊
  have err := SmoothLinearFieldEnvelope.floor_fraction n hn hb.le
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have one : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have tests := ((rate.const_mul 100).const_add 35).eventually_lt
    ((one.sub err).const_mul 102) surplus
  have charTest := ((rate.const_mul 200).const_add 70).eventually_lt (field.const_mul 102) characteristic
  have eLarge := (tiny.const_mul 2080).eventually_lt err (by simpa using hb)
  have enough := ((err.add tiny).const_mul 2).eventually_lt
    (LinearFieldBudgetLimit.floor_limit p n Q hQ hn field) (by simpa using budget)
  filter_upwards [tests,charTest,eLarge,enough,rate.eventually_const_lt hρ,
    (rate.const_mul 3).eventually_lt_const cap,err.eventually_lt_const bn] with i hs hc he hq hk hr hlen
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 35+100*((k i:ℝ)/n i)<102*(1-(e i:ℝ)/n i) at hs
  change 70+200*((k i:ℝ)/n i)<102*((p i:ℝ)/n i) at hc
  change 2080*(1/(n i:ℝ)) < (e i:ℝ)/n i at he
  change 2*((e i:ℝ)/n i+1/n i)<((p i/Q:ℕ):ℝ)/n i at hq
  change 3*((k i:ℝ)/n i)<1 at hr
  have en : e i≤n i := by exact_mod_cast ((div_lt_one ni).mp hlen).le
  field_simp at hs hc he hq hk hr
  have degree : 1≤k i := by exact_mod_cast hk
  have third : 3*k i≤n i := by rw [Nat.mul_comm]; exact_mod_cast hr.le
  have large : 2080<e i := by exact_mod_cast he
  have supply : 2*(e i+1)≤p i/Q := by exact_mod_cast hq.le
  have h₁ : 35*n i+100*k i + 102*e i < 102*n i := by
    exact_mod_cast (show 35*(n i:ℝ)+100*k i+102*e i<102*n i by linarith only [hs])
  have h₂ : 70*n i+200*k i<102*p i := by
    exact_mod_cast (show 70*(n i:ℝ)+200*k i<102*p i by linarith only [hc])
  have bound := upper (e:=e i) (x i) degree third large en (by unfold agreements;omega) (by
    intro u hu hu' eq
    have pd := Nat.le_of_dvd hu ((CharP.cast_eq_zero_iff (ZMod (p i)) (p i) u).mp eq)
    unfold agreements at hu'
    omega)
  apply le_mcaDeltaStar_of_good _ _
  · exact (div_le_one (by exact_mod_cast NeZero.pos (n i) : (0:ℝ≥0)<n i)).mpr (by exact_mod_cast en)
  · apply bound.trans
    rw [ZMod.card]
    exact (BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=(p i).Prime)).pos hQ).2 supply

/-- The limiting radius is exactly half the normalized budget, including the
packing and interpolation endpoints. -/
theorem limit (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hρ : 0<ρ) (cap : 3*ρ<1) (ha : 0<a) (index : 2*a=slope/Q)
    (pin : ρ+a<1) (pack : 1≤ρ+2*a) (surplus : 35+100*ρ≤102*(1-a))
    (characteristic : 70+200*ρ<102*slope) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (max_lt hs ha)
    have bp : 0<b := (le_max_right _ _).trans_lt lb
    have good := eventually_safe p n k x Q (by omega) hn field rate hρ cap bp (by linarith)
      (by linarith) characteristic (by linarith)
    have strict := (SmoothLinearFieldEnvelope.floor_fraction n hn bp.le).eventually_const_lt
      ((le_max_left _ _).trans_lt lb)
    filter_upwards [good,strict] with i hi lt
    exact lt.trans_le (by exact_mod_cast hi)
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (lt_min hs (show a<1-ρ by linarith))
    have bp := ha.trans lb
    have bad := ClosedTwoLinePhase.eventually_failing (fun i => ZMod (p i)) n k x Q two hn
      (by simpa only [ZMod.card] using field) rate hρ bp.le
      (by have := ub.trans_le (min_le_right _ _);linarith) (by linarith) (by linarith)
    have strict := (SmoothLinearFieldEnvelope.floor_fraction n hn bp.le).eventually_lt_const
      (ub.trans_le (min_le_left _ _))
    filter_upwards [bad,strict] with i hi lt
    exact lt_of_le_of_lt (by exact_mod_cast hi) lt

/-- At rate tending to one eighth the entire closed normalized budget interval
from 7/8 to 109/102 has the indicated threshold on every choice of domains. -/
theorem rate_eighth (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 (1/8)))
    (lower : 7/8≤ slope/Q) (upper : slope/Q≤109/102) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 (slope/Q/2)) := by
  have size : (2:ℝ) ≤ Q := by exact_mod_cast two
  have slopeLower := (le_div_iff₀ (by linarith : (0:ℝ)<Q)).mp lower
  apply limit p n k x Q two hn field rate (by norm_num) (by norm_num) (by linarith)
    (by ring) (by linarith) (by linarith) (by linarith) (by linarith)

end ProximityGap.QuadraticPrimePhase
#print axioms ProximityGap.QuadraticPrimePhase.limit
#print axioms ProximityGap.QuadraticPrimePhase.rate_eighth
