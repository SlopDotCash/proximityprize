/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldCapacityWindow
import ArkLib.Data.CodingTheory.ProximityGap.KKH26EntropyForm
import Mathlib.Analysis.SpecificLimits.Basic

/-! # The binary entropy boundary for exponential-size prime fields -/
set_option autoImplicit false
namespace ProximityGap.PrimeFieldEntropyPhase
open Filter Topology ReedSolomon MCAThresholdLedger PrimeFieldCapacityWindow
open scoped NNReal ENNReal

/-- Natural-log binomial entropy bounds with finite correction. -/
theorem choose_log_window {n a : ℕ} (ha : 0<a) (han : a<n) :
    Real.binEntropy ((a:ℝ)/n)-Real.log ((n:ℝ)+1)/n ≤ Real.log (n.choose a)/n ∧
      Real.log (n.choose a)/n ≤ Real.binEntropy ((a:ℝ)/n) := by
  have hn : 0<(n:ℝ) := by exact_mod_cast ha.trans han
  have hc : 0<(n.choose a:ℝ) := by exact_mod_cast Nat.choose_pos han.le
  have lower := ArkLib.ProximityGap.KKH26.exp_entropy_le_succ_mul_choose ha han
  have ll := Real.log_le_log (Real.exp_pos _) lower
  rw [Real.log_exp,Real.log_mul (by positivity) hc.ne'] at ll
  have term : a^a*(n-a)^(n-a)*n.choose a≤n^n := by
    have sum := add_pow a (n-a) n
    rw [Nat.add_sub_cancel' han.le] at sum
    rw [sum]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (a^j*(n-a)^(n-j)*n.choose j))
      (Finset.mem_range.mpr (by omega : a<n+1))
  have eh : (n.choose a : ℝ) ≤ Real.exp (n*Real.binEntropy ((a:ℝ)/n)) := by
    rw [ArkLib.ProximityGap.KKH26.exp_mul_binEntropy_eq ha han,le_div_iff₀]
    · rw [mul_comm]
      exact_mod_cast term
    · have hdiff : 0<((n-a:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt han
      have aa : 0<(a:ℝ) := by exact_mod_cast ha
      positivity
  have ul := Real.log_le_log hc eh
  rw [Real.log_exp] at ul
  constructor
  · rw [sub_le_iff_le_add,← add_div,le_div_iff₀ hn]
    linarith
  · exact (div_le_iff₀ hn).mpr (by linarith)

private theorem log_add_one_div {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    Tendsto (fun i => Real.log ((n i:ℝ)+1)/n i) atTop (𝓝 0) := by
  have top : Tendsto (fun i => (n i:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hn).atTop_add (tendsto_const_nhds (x:=(1:ℝ)))
  simpa [Function.comp_def,add_assoc] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp top

/-- The binomial exponent tends to binary entropy as the rate tends to `ρ`. -/
theorem choose_log_tendsto (n a : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (ha : ∀ᶠ i in atTop, 0<a i ∧ a i<n i) {ρ : ℝ}
    (rate : Tendsto (fun i => (a i:ℝ)/n i) atTop (𝓝 ρ)) :
    Tendsto (fun i => Real.log ((n i).choose (a i))/n i) atTop (𝓝 (Real.binEntropy ρ)) := by
  have he := Real.binEntropy_continuous.continuousAt.tendsto.comp rate
  have hl := he.sub (log_add_one_div hn)
  rw [sub_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl he
  · filter_upwards [ha] with i hi using (choose_log_window hi.1 hi.2).1
  · filter_upwards [ha] with i hi using (choose_log_window hi.1 hi.2).2

private theorem shifted_rate {n k : ℕ → ℕ} (hn : Tendsto n atTop atTop) {ρ : ℝ}
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    Tendsto (fun i => ((k i+1:ℕ):ℝ)/n i) atTop (𝓝 ρ) := by
  have h := rate.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  simpa [Nat.cast_add,add_div] using h

private theorem interior {n k : ℕ → ℕ} (hn : Tendsto n atTop atTop) {ρ : ℝ} (hρ : 0<ρ) (hr : ρ<1)
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    ∀ᶠ i in atTop, 0<k i ∧ k i+1<n i := by
  filter_upwards [rate.eventually_const_lt hρ,(shifted_rate hn rate).eventually_lt_const hr,
    hn.eventually_ge_atTop 1] with i kl ku ni
  have nn : 0<(n i:ℝ) := by exact_mod_cast ni
  have a := (div_pos_iff_of_pos_right nn).mp kl
  have b := (div_lt_one nn).mp ku
  exact ⟨by exact_mod_cast a,by exact_mod_cast b⟩

private theorem superpolynomial {n p : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c : ℝ} (hc : 0<c)
    (field : Tendsto (fun i => Real.log (p i)/n i) atTop (𝓝 c))
    (hp : ∀ i, 0<p i) : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i := by
  have top : Tendsto (fun i => (n i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have slow : Tendsto (fun i => Real.log (n i)/n i) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp top
  intro d
  have sd := slow.const_mul (d:ℝ)
  rw [mul_zero] at sd
  filter_upwards [sd.eventually_lt field hc,hn.eventually_ge_atTop 1] with i h hi
  have ni : 0<(n i:ℝ) := by exact_mod_cast hi
  change (d:ℝ)*(Real.log (n i)/(n i)) < _ at h
  rw [← mul_div_assoc,div_lt_div_iff_of_pos_right ni,← Real.log_pow] at h
  have pp : 0<(p i:ℝ) := by exact_mod_cast hp i
  exact_mod_cast ((Real.log_lt_log_iff (pow_pos ni _) pp).mp h).le

/-- Below the entropy exponent, the exact operational radius tends to capacity. -/
theorem below_entropy (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    {ρ c : ℝ} (hρ : 0<ρ) (hr : ρ<1) (hc : 0<c) (lo : c<Real.binEntropy ρ)
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (field : Tendsto (fun i => Real.log (p i)/n i) atTop (𝓝 c)) :
    Tendsto (fun i => radius (dom i) (k i)) atTop (𝓝 (1-ρ)) := by
  have hk := interior hn hρ hr rate
  have shifted := shifted_rate hn rate
  have counts := choose_log_tendsto n (fun i => k i+1) hn
    (hk.mono fun i h => ⟨by omega,h.2⟩) shifted
  apply radius_tendsto p n k dom hn (hk.mono fun i h => ⟨h.1,by omega⟩)
    (superpolynomial hn hc field fun i => (Fact.out : (p i).Prime).pos) _ rate
  filter_upwards [field.eventually_lt counts lo,hk] with i h hi
  have ni : 0<(n i:ℝ) := by exact_mod_cast (show 0<n i by omega)
  have pp : 0<(p i:ℝ) := by exact_mod_cast (Fact.out : (p i).Prime).pos
  have cp : 0<((n i).choose (k i+1):ℝ) := by exact_mod_cast Nat.choose_pos hi.2.le
  have near := (Real.log_lt_log_iff pp cp).mp ((div_lt_div_iff_of_pos_right ni).mp h)
  exact (show p i≤(n i).choose (k i+1) by exact_mod_cast near.le).trans
    (Nat.le_mul_of_pos_left _ (by decide))

/-- The full circuit budget suffices to make the radius exactly one. -/
theorem radius_one {p n k : ℕ} [Fact p.Prime] (dom : Fin n ↪ ZMod p)
    (hn : 0<n) (large : n.choose (k+1)*2^128≤p) : radius dom k=1 := by
  let _ : NeZero n := ⟨by omega⟩
  have good : epsMCA (F:=ZMod p) (code dom k : Set (Fin n → ZMod p)) 1 ≤ 1/(2:ℝ≥0∞)^128 := by
    apply (epsMCA_le_of_badCount_le _ _ (n.choose (k+1)) ?_).trans
    · have h := (BoundarySecurityBudget.count_ratio_le_iff (q:=Fintype.card (ZMod p)) (D:=2^128)
        Fintype.card_pos (by decide)).mpr (by simpa using (Nat.le_div_iff_mul_le (by decide : 0<2^128)).mpr large)
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using h
    · intro u; simpa using CircuitDensity.mca_count_le_choose dom k 1 (u 0) (u 1)
  have eq : mcaDeltaStar (F:=ZMod p) (code dom k : Set (Fin n → ZMod p)) (1/(2:ℝ≥0∞)^128)=1 :=
    le_antisymm (csSup_le' fun _ hmem => hmem.1) (le_mcaDeltaStar_of_good _ _ le_rfl good)
  unfold radius
  rw [eq]
  rfl

/-- Above the entropy exponent, the 128-bit security test eventually holds
at every radius, and the operational radius is exactly one. -/
theorem above_entropy (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    {ρ c : ℝ} (hρ : 0<ρ) (hr : ρ<1) (hi : Real.binEntropy ρ<c)
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (field : Tendsto (fun i => Real.log (p i)/n i) atTop (𝓝 c)) :
    ∀ᶠ i in atTop, radius (dom i) (k i)=1 := by
  have hk := interior hn hρ hr rate
  have counts := choose_log_tendsto n (fun i => k i+1) hn
    (hk.mono fun i h => ⟨by omega,h.2⟩) (shifted_rate hn rate)
  have zero := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn).const_mul (Real.log ((2:ℝ)^128))
  rw [mul_zero] at zero
  have cap := counts.add zero
  rw [add_zero] at cap
  filter_upwards [cap.eventually_lt field hi,hk] with i h ki
  have ni : 0<(n i:ℝ) := by exact_mod_cast (show 0<n i by omega)
  have pp : 0<(p i:ℝ) := by exact_mod_cast (Fact.out : (p i).Prime).pos
  have cp : 0<((n i).choose (k i+1):ℝ) := by exact_mod_cast Nat.choose_pos ki.2.le
  change Real.log ((n i).choose (k i+1))/n i + Real.log ((2:ℝ)^128)*(1/n i) < _ at h
  rw [← mul_div_assoc,mul_one,← add_div,div_lt_div_iff_of_pos_right ni,
    ← Real.log_mul cp.ne' (by positivity)] at h
  have ne := (Real.log_lt_log_iff (mul_pos cp (by positivity)) pp).mp h
  exact radius_one _ (by exact_mod_cast ni) (by exact_mod_cast ne.le)

#print axioms choose_log_window
#print axioms choose_log_tendsto
#print axioms below_entropy
#print axioms radius_one
#print axioms above_entropy
end ProximityGap.PrimeFieldEntropyPhase
