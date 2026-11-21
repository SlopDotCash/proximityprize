/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DoubleQuadraticThreshold
import ArkLib.Research.ProximityGap.Frontier.LinearFieldHalfDistancePlateau
import ArkLib.Research.ProximityGap.Frontier.ClosedTwoLinePhase

/-! # Three consecutive limiting regimes on arbitrary prime-field domains

For rate tending to ρ strictly between zero and one third, and a fixed
denominator Q≥2, write β for the limit of p/(Q n). Up to β = 4/3−2ρ
the threshold rises as β, stays at half the redundancy, and rises as β/2.
The theorem covers both transitions and the final endpoint.
-/
set_option autoImplicit false
namespace ProximityGap.DoubleQuadraticPhase
open Filter Topology MCAThresholdLedger DoubleQuadraticThreshold
open scoped NNReal ENNReal

variable (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ)

private theorem eventually_safe (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ b : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hρ : 0<ρ) (cap : 3*ρ<1) (hb : 0<b) (bn : b<1) (pack : 1<ρ+2*b)
    (surplus : 1+3*ρ<3*(1-b)) (characteristic : 2*(1-b)<slope)
    (budget : 2*b<slope/Q) :
    ∀ᶠ i in atTop, ((⌊b*(n i:ℝ)⌋₊:ℕ):ℝ≥0)/n i ≤ mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) := by
  let e i := ⌊b*(n i:ℝ)⌋₊
  have err := SmoothLinearFieldEnvelope.floor_fraction n hn hb.le
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have one : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have margin := (((one.add (rate.const_mul 3)).add (tiny.const_mul 16))).eventually_lt
    ((one.sub err).const_mul 3) (by simpa using surplus)
  have charTest := ((one.sub err).const_mul 2).eventually_lt field characteristic
  have supply := ((err.add tiny).const_mul 2).eventually_lt (LinearFieldBudgetLimit.floor_limit p n Q hQ hn field)
    (by simpa using budget)
  have packed := (rate.add (err.const_mul 2)).eventually_const_lt pack
  filter_upwards [margin,charTest,supply,packed,tiny.eventually_lt rate hρ,
    (rate.const_mul 3).eventually_lt_const cap,err.eventually_lt_const bn,
    (tendsto_atTop.mp hn 65536)] with i hs hc hq hp hk hr hlen big
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1+3*((k i:ℝ)/n i)+16*(1/n i)<3*(1-(e i:ℝ)/n i) at hs
  change 2*(1-(e i:ℝ)/n i)<(p i:ℝ)/n i at hc
  change 2*((e i:ℝ)/n i+1/n i)<((p i/Q:ℕ):ℝ)/n i at hq
  change 1<(k i:ℝ)/n i+2*((e i:ℝ)/n i) at hp
  change 3*((k i:ℝ)/n i)<1 at hr
  change 1/(n i:ℝ)<(k i:ℝ)/n i at hk
  have en : e i≤n i := by exact_mod_cast ((div_lt_one ni).mp hlen).le
  field_simp at hs hc hq hp hr hk
  have degree : 2≤k i := by exact_mod_cast hk
  have third : 3*k i≤n i := by exact_mod_cast (show 3*(k i:ℝ)≤n i by linarith only [hr])
  have count : 2*(e i+1)≤p i/Q := by exact_mod_cast hq.le
  have geometry : n i+3*k i+16+3*e i<3*n i := by
    exact_mod_cast (show (n i:ℝ)+3*k i+16+3*e i<3*n i by linarith only [hs])
  have fieldRoom : 2*n i < p i+2*e i := by
    exact_mod_cast (show 2*(n i:ℝ)<p i+2*e i by linarith only [hc])
  have space : n i≤k i+2*e i := by
    exact_mod_cast (show (n i:ℝ)≤k i+2*e i by linarith only [hp])
  have bounded := upper (e:=e i) (x i) big degree third en (by omega) (by unfold agreements;omega) (by
    intro u hu bound zero
    have pd := Nat.le_of_dvd hu ((CharP.cast_eq_zero_iff (ZMod (p i)) (p i) u).mp zero)
    omega)
  apply le_mcaDeltaStar_of_good _ _
  · exact (div_le_one (by exact_mod_cast NeZero.pos (n i) : (0:ℝ≥0)<n i)).mpr (by exact_mod_cast en)
  · apply bounded.trans
    rw [ZMod.card]
    exact (BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=(p i).Prime)).pos hQ).2 count

/-- In the final regime the largest safe grid radii approach half the
normalized budget, including equality in either limiting inequality. -/
theorem two_heads (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hρ : 0<ρ) (cap : 3*ρ<1) (index : 2*a=slope/Q)
    (packing : 1≤ρ+2*a) (geometry : 1+3*ρ≤3*(1-a)) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  rcases packing.eq_or_lt with boundary|interior
  · have aeq : (1-ρ)/2=a := by linarith
    rw [←aeq]
    exact LinearFieldHalfDistancePlateau.plateau p n k x Q (by omega) hn hρ (by linarith)
      field rate (by linarith) (by linarith)
  have ha : 0<a := by linarith
  have hQ : (2:ℝ)≤Q := by exact_mod_cast two
  have slopeLower : 2*a*(Q:ℝ)=slope := (eq_div_iff (by linarith : (Q:ℝ)≠0)).mp index
  have fieldLarge : 2*(1-ρ)<slope := by nlinarith [mul_nonneg (by linarith : (0:ℝ)≤Q-2) ha.le]
  apply tendsto_order.mpr
  constructor
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (max_lt hs (show (1-ρ)/2<a by linarith))
    have fit := (le_max_right _ _).trans_lt lb
    have bp : 0<b := by linarith
    have good := eventually_safe p n k x Q (by omega) hn field rate hρ cap bp (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
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

/-- A single expression gives the normalized limiting MCA radius on all
three regimes, for every positive and possibly varying interleaving width. -/
theorem curve (two : 2≤Q) (hn : Tendsto n atTop atTop) {slope ρ : ℝ}
    (field : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (hρ : 0<ρ) (cap : 3*ρ<1) (endBudget : slope/Q ≤ 4/3-2*ρ)
    (width : ℕ → ℕ) [∀ i, NeZero (width i)] :
    let β := slope/Q
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) ((ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) ^⋈ (Fin (width i))) (1/(Q:ℝ≥0∞)):ℝ))
      atTop (𝓝 (min β (max ((1-ρ)/2) (β/2)))) := by
  dsimp only
  simp only [mcaDeltaStar_interleaved_eq]
  by_cases small : slope/Q < (1-ρ)/2
  · rw [max_eq_left (by linarith),min_eq_left small.le]
    have hk : ∀ᶠ i in atTop, 1≤k i := by
      filter_upwards [rate.eventually_const_lt hρ] with i hi
      by_contra! h
      simp [show k i=0 by omega] at hi
    exact (LinearFieldBudgetLimit.eventually_exact p n k x Q (by omega) hk hn field rate (by linarith)).2
  by_cases plateau : slope/Q ≤ 1-ρ
  · rw [max_eq_left (by linarith),min_eq_right (by linarith)]
    exact LinearFieldHalfDistancePlateau.plateau p n k x Q (by omega) hn hρ (by linarith)
      field rate (by linarith) plateau
  · rw [max_eq_right (by linarith),min_eq_right (by linarith)]
    exact two_heads p n k x Q two hn field rate hρ cap (by ring) (by linarith) (by linarith)

end ProximityGap.DoubleQuadraticPhase
#print axioms ProximityGap.DoubleQuadraticPhase.two_heads
#print axioms ProximityGap.DoubleQuadraticPhase.curve
