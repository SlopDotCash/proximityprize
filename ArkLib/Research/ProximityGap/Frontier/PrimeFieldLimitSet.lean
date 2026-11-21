/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldCriticalEntropy

/-! # Complete classification of critical operational-radius limits -/
set_option autoImplicit false
namespace ProximityGap.PrimeFieldLimitSet
open Filter Topology ReedSolomon MCAThresholdLedger PrimeFieldCapacityWindow PrimeFieldCriticalEntropy
open scoped NNReal ENNReal

/-- In every nontrivial finite instance the supremum is `1` or is at most the
first radius in the constant `k+1`-agreement region. -/
theorem finite_dichotomy {p n k : ℕ} [Fact p.Prime] (h : k<n) (D : Fin n ↪ ZMod p) :
    radius D k=1 ∨ radius D k≤1-((k:ℝ)+1)/n := by
  let _ : NeZero n := ⟨by omega⟩
  let C := (code D k : Set (Fin n → ZMod p))
  let ε : ℝ≥0∞ := 1/2^128
  by_cases ok : epsMCA (F:=ZMod p) C 1≤ε
  · left
    have eq : mcaDeltaStar (F:=ZMod p) C ε=1 := le_antisymm (csSup_le' fun _ hm => hm.1)
      (le_mcaDeltaStar_of_good _ _ le_rfl ok)
    exact congrArg ((↑) : ℝ≥0 → ℝ) eq
  · right
    have hn : 0<(n:ℝ≥0) := by exact_mod_cast NeZero.pos n
    have hl : ((k+1:ℕ):ℝ≥0)/n≤1 := (div_le_one hn).mpr (by exact_mod_cast h)
    let r : ℝ≥0 := 1-((k+1:ℕ):ℝ≥0)/n
    have bound : (1-r)*(Fintype.card (Fin n):ℝ≥0)≤((k+1:ℕ):ℝ≥0) := by
      rw [Fintype.card_fin,tsub_tsub_cancel_of_le hl,div_mul_cancel₀ _ hn.ne']
    have p0 := epsMCA_eq_epsMCA_one_of_le_succ D k (δ:=r) (by simpa using bound)
    change epsMCA (F:=ZMod p) C r=epsMCA (F:=ZMod p) C 1 at p0
    rw [← p0] at ok
    have realBound : radius D k≤(r:ℝ) := NNReal.coe_le_coe.mpr (mcaDeltaStar_le_of_bad _ _ (lt_of_not_ge ok))
    dsimp only [r] at realBound
    rw [NNReal.coe_sub hl] at realBound
    simpa using realBound

private theorem capacity_lower {p n k : ℕ} [Fact p.Prime] {g : ℝ} (hg : 0<g)
    (len : capacityLineLength g≤n) (hk : 0<k) (hkn : k<n)
    (hp : (2:ℝ)^128*(capacityLineConstant g*(n:ℝ)^(capacityLineDerivativeOrder g+1)) ≤ p)
    (D : Fin n ↪ ZMod p) : 1-(k:ℝ)/n-g≤radius D k := by
  let _ : NeZero n := ⟨by omega⟩
  change capacityRadius g n k≤_
  by_cases neg : capacityRadius g n k≤0
  · exact neg.trans (NNReal.coe_nonneg _)
  let r : ℝ≥0 := ⟨capacityRadius g n k,le_of_not_ge neg⟩
  have one : r≤1 := by
    change capacityRadius g n k≤(1:ℝ)
    unfold capacityRadius
    have q : 0≤(k:ℝ)/n := by positivity
    linarith
  let _ : SampleableType (ZMod p) := SampleableType.ofFintype _
  have good := PrimeFieldCapacityGap.prime_line_security128 hg len hk hkn.le le_rfl hp D
  have eq : ENNReal.ofReal (1/(2:ℝ)^128)=1/(2:ℝ≥0∞)^128 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_pow (by norm_num)]; norm_num
  rw [eq] at good
  apply NNReal.coe_le_coe.mpr (le_mcaDeltaStar_of_good _ _ one ?_)
  rw [epsMCA_eq_mcaError];exact good

private theorem eventually_lower (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (D : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i) (big : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    {g : ℝ} (hg : 0<g) : ∀ᶠ i in atTop, 1-(k i:ℝ)/n i-g≤radius (D i) (k i) := by
  let K := (2:ℝ)^128*capacityLineConstant g
  let d := capacityLineDerivativeOrder g+1
  filter_upwards [hn.eventually_ge_atTop (capacityLineLength g),hn.eventually_ge_atTop ⌈K⌉₊,big (d+1),hk] with i hl hK hp hi
  apply capacity_lower hg hl hi.1 hi.2 _ (D i)
  have coeff : K≤(n i:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hK)
  calc _ = (n i:ℝ)^d*K := by dsimp [d,K];ring
       _ ≤ (n i:ℝ)^d*n i := mul_le_mul_of_nonneg_left coeff (by positivity)
       _ = ((n i)^(d+1):ℕ) := by rw [Nat.cast_pow,pow_succ (n i:ℝ) d]
       _ ≤ _ := by exact_mod_cast hp

/-- Every convergent sequence of operational radii in superpolynomial prime
fields limits to capacity or one. There is no upper field-size assumption. -/
theorem limiting_dichotomy (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (D : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i) (big : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    {ρ L : ℝ} (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (rad : Tendsto (fun i => radius (D i) (k i)) atTop (𝓝 L)) : L=1-ρ ∨ L=1 := by
  have cap := (tendsto_const_nhds (x:=(1:ℝ))).sub rate
  have b : 1-ρ≤L := by
    by_contra! h
    let g := (1-ρ-L)/2
    have hg : 0<g := by dsimp [g];linarith
    have le := le_of_tendsto_of_tendsto (cap.sub (tendsto_const_nhds (x:=g))) rad
      (eventually_lower p n k D hn hk big hg)
    dsimp [g] at le
    linarith
  by_cases eq : L=1-ρ
  · exact Or.inl eq
  have sep := cap.eventually_lt rad (lt_of_le_of_ne b (Ne.symm eq))
  have flat : ∀ᶠ i in atTop, radius (D i) (k i)=1 := by
    filter_upwards [sep,hk] with i near hi
    rcases finite_dichotomy hi.2 (D i) with yes|no
    · exact yes
    · have m : (k i:ℝ)/n i≤((k i:ℝ)+1)/n i := by gcongr;linarith
      change 1-(k i:ℝ)/n i<radius (D i) (k i) at near
      linarith
  exact Or.inr (tendsto_nhds_unique rad (tendsto_const_nhds.congr' (flat.mono fun _ h => h.symm)))

/-- The same two-point restriction applies to every convergent subsequence. -/
theorem subsequential_dichotomy (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (D : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i) (big : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    {ρ L : ℝ} (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (σ : ℕ → ℕ) (inc : StrictMono σ)
    (rad : Tendsto (fun i => radius (D (σ i)) (k (σ i))) atTop (𝓝 L)) : L=1-ρ ∨ L=1 :=
  limiting_dichotomy (fun i => p (σ i)) (fun i => n (σ i)) (fun i => k (σ i)) (fun i => D (σ i))
    (hn.comp inc.tendsto_atTop) (inc.tendsto_atTop.eventually hk)
    (fun d => inc.tendsto_atTop.eventually (big d)) (rate.comp inc.tendsto_atTop) rad

private theorem superpolynomial {n p : ℕ → ℕ} (hn : Tendsto n atTop atTop) {c : ℝ} (hc : 0<c)
    (field : Tendsto (fun i => Real.log (p i)/n i) atTop (𝓝 c)) (hp : ∀ i, 0<p i) :
    ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i := by
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

/-- Attainable limits for fixed lengths and dimensions under a critical-exponent
prime-field choice and arbitrary evaluation embeddings. -/
def CriticalLimits (n k : ℕ → ℕ) (ρ : ℝ) : Set ℝ :=
  {L | ∃ (p : ℕ → ℕ) (hp : ∀ i, Fact (p i).Prime), letI := hp
       ∃ D : ∀ i, Fin (n i) ↪ ZMod (p i),
         Tendsto (fun i => Real.log (p i)/n i) atTop (𝓝 (Real.binEntropy ρ)) ∧
         Tendsto (fun i => radius (D i) (k i)) atTop (𝓝 L)}

/-- At each fixed interior limiting rate the attainable critical limiting set
is exactly `{1−ρ, 1}`, for any prescribed lengths and dimensions as below. -/
theorem critical_limits_eq (n k : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hk : ∀ i, k i+1<n i) {ρ : ℝ} (hρ : 0<ρ) (hr : ρ<1)
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    CriticalLimits n k ρ={1-ρ,1} := by
  classical
  ext L
  change (_:Prop) ↔ L=1-ρ ∨ L=1
  constructor
  · rintro ⟨p,hp,D,field,rad⟩
    let _ := hp
    apply limiting_dichotomy p n k D hn _ (superpolynomial hn (Real.binEntropy_pos hρ hr) field
      (fun i => (hp i).out.pos)) rate rad
    filter_upwards [rate.eventually_const_lt hρ] with i h
    have ni : 0<(n i:ℝ) := by exact_mod_cast (show 0<n i by have := hk i;omega)
    exact ⟨by exact_mod_cast (div_pos_iff_of_pos_right ni).mp h,by have := hk i;omega⟩
  · let P := fun i => upperPrime (1*(n i).choose (k i+1))
    let Q := fun i => upperPrime (2^128*(n i).choose (k i+1))
    let D := fun i => Classical.choice (has_domain (hk i) (by decide : 0<1))
    let E := fun i => Classical.choice (has_domain (hk i) (by decide : 0<2^128))
    obtain ⟨pgr,qgr,lp,qe,_⟩ := critical_nonuniqueness n k hn hk hρ hr rate D E
    rintro (rfl|rfl)
    · exact ⟨P,fun i => prime_fact _,D,pgr,lp⟩
    · exact ⟨Q,fun i => prime_fact _,E,qgr,tendsto_const_nhds.congr' (qe.mono fun _ h => h.symm)⟩

#print axioms finite_dichotomy
#print axioms limiting_dichotomy
#print axioms subsequential_dichotomy
#print axioms critical_limits_eq
end ProximityGap.PrimeFieldLimitSet
