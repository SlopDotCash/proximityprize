/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldCapacityGap
import ArkLib.Research.ProximityGap.Frontier.CircuitBudgetRadius
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityMCA
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Topology.Instances.Real.Lemmas

/-! # A two-sided capacity window for the operational prime-field MCA radius -/
set_option autoImplicit false
namespace ProximityGap.PrimeFieldCapacityWindow
open Filter Topology ReedSolomon MCAThresholdLedger
open scoped NNReal ENNReal

/-- The binomial coefficient always dominates the power of two indexed by
its distance from the nearer end of the row. -/
theorem pow_min_le_choose {n a : ℕ} (ha : a≤n) : 2^min a (n-a) ≤ n.choose a := by
  have central (m : ℕ) : 2^m ≤ (2*m).choose m := by
    induction m with
    | zero => decide
    | succ m ih =>
      have step := ih.trans (Nat.choose_le_choose m (show 2*m≤2*m+1 by omega))
      rw [show 2*(m+1)=(2*m+1)+1 by omega,Nat.choose_succ_succ,Nat.choose_symm_half,pow_succ]
      omega
  rcases le_total a (n-a) with h|h
  · rw [min_eq_left h]
    exact (central a).trans (Nat.choose_le_choose a (by omega))
  · rw [min_eq_right h,← Nat.choose_symm ha]
    exact (central (n-a)).trans (Nat.choose_le_choose (n-a) (by omega))

/-- The prime-field line-MCA operational radius for success tolerance `2⁻¹²⁸`,
as a real number. -/
noncomputable def radius {p n : ℕ} [Fact p.Prime] (dom : Fin n ↪ ZMod p) (k : ℕ) : ℝ :=
  (mcaDeltaStar (F:=ZMod p) (code dom k : Set (Fin n → ZMod p)) (1/(2:ℝ≥0∞)^128) : ℝ≥0)

/-- The last `k+1` agreements cannot be secure when the field fits within the
binomial collision budget. The conclusion bounds the supremum of real radii. -/
theorem upper {p n k : ℕ} [Fact p.Prime] (hk : 0<k) (hkn : k<n)
    (small : p≤(2^128-1)*n.choose (k+1)) (dom : Fin n ↪ ZMod p) :
    radius dom k ≤ 1-((k:ℝ)+1)/n := by
  let _ : NeZero n := ⟨by omega⟩
  have hn : 0<(n:ℝ≥0) := by exact_mod_cast (NeZero.pos n)
  have hrat : ((k+1:ℕ):ℝ≥0)/n≤1 := (div_le_one hn).mpr (by exact_mod_cast hkn)
  let r : ℝ≥0 := 1-((k+1:ℕ):ℝ≥0)/n
  have hr : (1-r)*(Fintype.card (Fin n) : ℝ≥0)=((k+1:ℕ):ℝ≥0) := by
    rw [Fintype.card_fin,tsub_tsub_cancel_of_le hrat,div_mul_cancel₀ _ hn.ne']
  have hb := CircuitBudgetRadius.bad_one_of_card_le (D:=2^128) dom hk hkn (by decide) (by simpa using small)
  have e := epsMCA_eq_epsMCA_one_of_le_succ dom k (δ:=r) (by simpa using hr.le)
  rw [← e] at hb
  have bound := mcaDeltaStar_le_of_bad _ _ (lt_of_not_ge hb)
  have br : radius dom k ≤ (r:ℝ) := by
    change (_:ℝ≥0) ≤ _
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using bound
  dsimp only [r] at br
  rw [NNReal.coe_sub hrat] at br
  simpa using br

/-- Finite sandwich at any fixed positive slack. Both field-size tests are
uniform in the evaluation embedding. -/
theorem sandwich {p n k : ℕ} [Fact p.Prime] {gap : ℝ} (hg : 0<gap)
    (len : capacityLineLength gap≤n) (hk : 0<k) (hkn : k<n)
    (large : (2:ℝ)^128*(capacityLineConstant gap*(n:ℝ)^(capacityLineDerivativeOrder gap+1))≤p)
    (small : p≤(2^128-1)*n.choose (k+1)) (dom : Fin n ↪ ZMod p) :
    1-(k:ℝ)/n-gap ≤ radius dom k ∧ radius dom k ≤ 1-((k:ℝ)+1)/n := by
  let _ : NeZero n := ⟨by omega⟩
  refine ⟨?_,upper hk hkn small dom⟩
  have pos : 0 ≤ radius dom k := NNReal.coe_nonneg _
  change capacityRadius gap n k ≤ _
  by_cases neg : capacityRadius gap n k≤0
  · exact neg.trans pos
  let r : ℝ≥0 := ⟨capacityRadius gap n k,le_of_not_ge neg⟩
  have cap : r≤1 := by
    change capacityRadius gap n k ≤ (1:ℝ)
    unfold capacityRadius
    have hpos : 0≤(k:ℝ)/n := by positivity
    linarith
  let _ : SampleableType (ZMod p) := SampleableType.ofFintype _
  have h := PrimeFieldCapacityGap.prime_line_security128 hg len hk hkn.le le_rfl large dom
  have eq : ENNReal.ofReal (1/(2:ℝ)^128) = 1/(2:ℝ≥0∞)^128 := by
    rw [ENNReal.ofReal_div_of_pos (by positivity),ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [eq] at h
  have good : epsMCA (F:=ZMod p) (code dom k : Set (Fin n → ZMod p)) r ≤ 1/(2:ℝ≥0∞)^128 := by
    rw [epsMCA_eq_mcaError]; exact h
  exact NNReal.coe_le_coe.mpr (le_mcaDeltaStar_of_good _ _ cap good)

/-- For arbitrarily chosen embeddings and rates, the difference between
capacity and the operational radius tends to zero. The size hypotheses only
involve field size, length and dimension. -/
theorem capacity_gap_tendsto_of_binomial (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i)
    (large : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    (small : ∀ᶠ i in atTop, p i≤(2^128-1)*(n i).choose (k i+1)) :
    Tendsto (fun i => (1-(k i:ℝ)/n i)-radius (dom i) (k i)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let g := ε/2
  have hg : 0<g := by dsimp [g]; positivity
  let b := (2:ℝ)^128*capacityLineConstant g
  let d := capacityLineDerivativeOrder g+1
  filter_upwards [hn.eventually_ge_atTop (capacityLineLength g),hn.eventually_ge_atTop ⌈b⌉₊,
    large (d+1),hk,small] with i len hnC pn ki pu
  have coeff : b≤(n i:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
  have lc : (2:ℝ)^128*(capacityLineConstant g*(n i:ℝ)^d) ≤ p i := calc
    _ = (n i:ℝ)^d*b := by dsimp [b]; ring
    _ ≤ (n i:ℝ)^d*(n i) := mul_le_mul_of_nonneg_left coeff (by positivity)
    _ = ((n i)^(d+1):ℕ) := by rw [Nat.cast_pow,pow_succ (n i:ℝ) d]
    _ ≤ _ := by exact_mod_cast pn
  obtain ⟨l,u⟩ := sandwich hg len ki.1 ki.2 lc pu (dom i)
  have top : (k i:ℝ)/(n i)≤((k i:ℝ)+1)/(n i) := by gcongr; linarith
  rw [Real.dist_eq,sub_zero,abs_lt]
  dsimp [g] at l
  constructor <;> linarith

/-- For arbitrarily chosen embeddings and rates, the difference between
capacity and the operational radius tends to zero. The size hypotheses only
involve field size, length and dimension. -/
theorem capacity_gap_tendsto (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i)
    (large : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    (small : ∀ᶠ i in atTop, p i≤2^min (k i+1) (n i-k i-1)) :
    Tendsto (fun i => (1-(k i:ℝ)/n i)-radius (dom i) (k i)) atTop (𝓝 0) := by
  apply capacity_gap_tendsto_of_binomial p n k dom hn hk large
  filter_upwards [hk,small] with i ki pu
  have cc := pow_min_le_choose (n:=n i) (a:=k i+1) (by omega)
  rw [show n i-(k i+1)=n i-k i-1 by omega] at cc
  exact (pu.trans cc).trans (Nat.le_mul_of_pos_left _ (by decide))

/-- If in addition the rates converge to `ρ`, the operational radii converge
to `1−ρ`, with no smoothness restriction on the domains. -/
theorem radius_tendsto (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i)
    (large : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    (small : ∀ᶠ i in atTop, p i≤(2^128-1)*(n i).choose (k i+1))
    {ρ : ℝ} (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    Tendsto (fun i => radius (dom i) (k i)) atTop (𝓝 (1-ρ)) := by
  have base := (tendsto_const_nhds (x:=(1:ℝ))).sub rate
  have both := base.sub (capacity_gap_tendsto_of_binomial p n k dom hn hk large small)
  simpa only [Pi.sub_apply,sub_sub_cancel,sub_zero] using both

/-- The equality holds separately at each finite length and positive width. -/
theorem interleaved_radius_eq {p n : ℕ} [Fact p.Prime] [NeZero n] (dom : Fin n ↪ ZMod p)
    (k t : ℕ) [NeZero t] :
    (mcaDeltaStar (F:=ZMod p) (A:=Fin t→ZMod p)
      ((code dom k : Set (Fin n → ZMod p))^⋈ (Fin t)) (1/(2:ℝ≥0∞)^128) : ℝ) = radius dom k := by
  have sets : mcaGoodRadii (F:=ZMod p) (A:=Fin t→ZMod p)
      ((code dom k : Set (Fin n → ZMod p))^⋈ (Fin t)) (1/(2:ℝ≥0∞)^128) =
      mcaGoodRadii (F:=ZMod p) (code dom k : Set (Fin n → ZMod p)) (1/(2:ℝ≥0∞)^128) := by
    ext δ
    change (_ ∧ _ ≤ _) ↔ (_ ∧ _ ≤ _)
    rw [epsMCA_interleaved_eq]
  unfold radius mcaDeltaStar
  rw [sets]

/-- The same limit holds even for interleaving widths that vary with length. -/
theorem interleaved_gap_tendsto (p n k t : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (t i)]
    (dom : ∀ i, Fin (n i) ↪ ZMod (p i)) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, 0<k i ∧ k i<n i)
    (large : ∀ d : ℕ, ∀ᶠ i in atTop, (n i)^d≤p i)
    (small : ∀ᶠ i in atTop, p i≤2^min (k i+1) (n i-k i-1)) :
    Tendsto (fun i => (1-(k i:ℝ)/n i)-(mcaDeltaStar (F:=ZMod (p i)) (A:=Fin (t i)→ZMod (p i))
      ((code (dom i) (k i) : Set (Fin (n i) → ZMod (p i)))^⋈ (Fin (t i))) (1/(2:ℝ≥0∞)^128) : ℝ))
      atTop (𝓝 0) := by
  apply (capacity_gap_tendsto p n k dom hn hk large small).congr'
  filter_upwards [hk] with i ki
  let _ : NeZero (n i) := ⟨by omega⟩
  rw [interleaved_radius_eq]

#print axioms interleaved_radius_eq
#print axioms interleaved_gap_tendsto
#print axioms pow_min_le_choose
#print axioms capacity_gap_tendsto_of_binomial
#print axioms radius_tendsto
#print axioms upper
#print axioms sandwich
#print axioms capacity_gap_tendsto
end ProximityGap.PrimeFieldCapacityWindow
