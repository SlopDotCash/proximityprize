/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldEntropyPhase
import Mathlib.NumberTheory.Bertrand

/-! # Two different outcomes at the same critical field-size exponent -/
set_option autoImplicit false
namespace ProximityGap.PrimeFieldCriticalEntropy
open Filter Topology ReedSolomon PrimeFieldCapacityWindow PrimeFieldEntropyPhase
open scoped NNReal ENNReal

noncomputable def upperPrime (m : ℕ) := (Nat.exists_prime_lt_and_le_two_mul (max m 1) (by omega)).choose
instance prime_fact (m : ℕ) : Fact (upperPrime m).Prime :=
  ⟨(Nat.exists_prime_lt_and_le_two_mul (max m 1) (by omega)).choose_spec.1⟩

private theorem size {m : ℕ} (hm : 0 < m) : m<upperPrime m ∧ upperPrime m≤2*m := by
  have hh := (Nat.exists_prime_lt_and_le_two_mul (max m 1) (by omega)).choose_spec.2
  change max m 1<upperPrime m ∧ upperPrime m≤2*max m 1 at hh
  simpa [max_eq_left (show 1 ≤ m by omega)] using hh

private theorem top_le_choose {n a : ℕ} (h : 0<a) (ha : a<n) : n ≤ n.choose a := by
  induction n generalizing a with
  | zero => omega
  | succ n ih =>
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    by_cases eq : a=0
    · simp [eq]
    rw [Nat.choose_succ_succ]
    have first := ih (show 0<a by omega) (show a<n by omega)
    have other := Nat.choose_pos (show a+1≤n by omega)
    change n+1 ≤ n.choose a + n.choose (a+1)
    omega

/-- The critical primes actually admit length-`n` embeddings. -/
theorem has_domain {n k A : ℕ} (h : k+1<n) (ha : 0<A) :
    Nonempty (Fin n ↪ ZMod (upperPrime (A*n.choose (k+1)))) := by
  have x := top_le_choose (Nat.succ_pos k) h
  have b := (size (Nat.mul_pos ha (Nat.choose_pos h.le))).1
  have q : n≤upperPrime (A*n.choose (k+1)) := (x.trans (Nat.le_mul_of_pos_left _ ha)).trans b.le
  exact Function.Embedding.nonempty_of_card_le (by simpa using q)

/-- Scaling the binomial by any fixed positive factor before choosing the
Bertrand prime preserves its critical exponent. -/
theorem critical_growth (n k : ℕ → ℕ) (A : ℕ) (ha : 0<A) (hn : Tendsto n atTop atTop)
    (hk : ∀ᶠ i in atTop, k i+1<n i) {ρ : ℝ}
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) :
    Tendsto (fun i => Real.log (upperPrime (A*(n i).choose (k i+1)))/n i) atTop (𝓝 (Real.binEntropy ρ)) := by
  have r := rate.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  have shifted : Tendsto (fun i => ((k i+1:ℕ):ℝ)/n i) atTop (𝓝 ρ) := by simpa [add_div] using r
  have base := choose_log_tendsto n (fun i => k i+1) hn (hk.mono fun i h => ⟨Nat.succ_pos _,h⟩) shifted
  have zero := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn).const_mul (Real.log (2*(A:ℝ)))
  rw [mul_zero] at zero
  have bound := base.add zero
  rw [add_zero] at bound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' base bound
  · filter_upwards [hk] with i hi
    have xp := Nat.choose_pos hi.le
    have ne := (Nat.le_mul_of_pos_left ((n i).choose (k i+1)) ha).trans (size (Nat.mul_pos ha xp)).1.le
    exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast xp) (by exact_mod_cast ne)) (by positivity)
  · filter_upwards [hk] with i hi
    have xp := Nat.choose_pos hi.le
    have w := (size (Nat.mul_pos ha xp)).2
    have op : 0<upperPrime (A*(n i).choose (k i+1)) := (prime_fact _).out.pos
    have r2 := Real.log_le_log (show (0:ℝ)<upperPrime (A*(n i).choose (k i+1)) by exact_mod_cast op)
      (show (upperPrime (A*(n i).choose (k i+1)):ℝ)≤((n i).choose (k i+1):ℝ)*(2*A) by
        have cc : upperPrime (A*(n i).choose (k i+1)) ≤ (n i).choose (k i+1)*(2*A) := by simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using w
        exact_mod_cast cc)
    rw [Real.log_mul (by exact_mod_cast xp.ne') (by positivity)] at r2
    simpa [div_eq_mul_inv,add_mul] using div_le_div_of_nonneg_right r2 (by positivity : 0≤(n i:ℝ))

/-- The lower critical prime lies in the exact capacity-predecessor budget
window; the upper critical prime already makes the operational radius one. -/
theorem two_finite {n k : ℕ} (big : 2^128≤k+1) (h : k+1<n)
    (D : Fin n ↪ ZMod (upperPrime (1*n.choose (k+1))))
    (E : Fin n ↪ ZMod (upperPrime (2^128*n.choose (k+1)))) :
    radius D k=1-((k:ℝ)+1)/n ∧ radius E k=1 := by
  let _ : NeZero n := ⟨by omega⟩
  let _ : SampleableType (ZMod (upperPrime (1*n.choose (k+1)))) := SampleableType.ofFintype _
  have apos := Nat.choose_pos h.le
  have q := size (Nat.mul_pos (by decide : 0<1) apos)
  have low : n.choose (k+1)/(k+1)≤upperPrime (1*n.choose (k+1))/2^128 :=
    (Nat.div_le_div_left (a:=n.choose (k+1)) big (by decide)).trans
      (Nat.div_le_div_right (by simpa only [one_mul] using q.1.le))
  have high : upperPrime (1*n.choose (k+1))≤(2^128-1)*n.choose (k+1) :=
    q.2.trans (by rw [one_mul];exact Nat.mul_le_mul_right _ (by decide))
  have cert := CircuitBudgetRadius.wide_deltaStar (k:=k) (D:=2^128) D (by omega) (by omega) (by decide)
    (by simpa using low) (by simpa using high)
  have hn : 0<(n:ℝ≥0) := by exact_mod_cast (NeZero.pos n)
  have b : ((k+1:ℕ):ℝ≥0)/n≤1 := (div_le_one hn).mpr (by exact_mod_cast h.le)
  constructor
  · unfold radius
    simp only [Nat.cast_pow,Nat.cast_ofNat] at cert
    rw [cert,NNReal.coe_sub b];simp
  · exact radius_one E (by omega) (by simpa only [mul_comm] using
      (size (Nat.mul_pos (by decide : 0<2^128) apos)).1.le)

/-- The fields at opposite sides of the finite budget have identical limiting
normalized logarithms, but for every pair of embeddings their operational
radii exhibit the two different limits at any interior limiting rate. -/
theorem critical_nonuniqueness (n k : ℕ → ℕ) (hn : Tendsto n atTop atTop)
    (hk : ∀ i, k i+1<n i) {ρ : ℝ} (hρ : 0<ρ) (_hr : ρ<1)
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (D : ∀ i, Fin (n i) ↪ ZMod (upperPrime (1*(n i).choose (k i+1))))
    (E : ∀ i, Fin (n i) ↪ ZMod (upperPrime (2^128*(n i).choose (k i+1)))) :
    Tendsto (fun i => Real.log (upperPrime (1*(n i).choose (k i+1)))/n i) atTop (𝓝 (Real.binEntropy ρ)) ∧
    Tendsto (fun i => Real.log (upperPrime (2^128*(n i).choose (k i+1)))/n i) atTop (𝓝 (Real.binEntropy ρ)) ∧
    Tendsto (fun i => radius (D i) (k i)) atTop (𝓝 (1-ρ)) ∧
    (∀ᶠ i in atTop, radius (E i) (k i)=1) ∧ 1-ρ≠1 := by
  have whole : ∀ᶠ i in atTop, k i+1<n i := Eventually.of_forall hk
  have half := half_pos hρ
  have big : ∀ᶠ i in atTop, 2^128≤k i+1 := by
    filter_upwards [rate.eventually_const_lt (half_lt_self hρ),hn.eventually_ge_atTop ⌈(2:ℝ)^128/(ρ/2)⌉₊] with i h ni
    have pos : (0:ℝ)<n i := by exact_mod_cast (show 0<n i by have := hk i;omega)
    have coef : (2:ℝ)^128/(ρ/2)≤n i := (Nat.le_ceil _).trans (by exact_mod_cast ni)
    have l := (div_le_iff₀ half).mp coef
    have u := (lt_div_iff₀ pos).mp h
    have out : (2:ℝ)^128 < k i := by linarith
    exact (show 2^128≤k i by exact_mod_cast out.le).trans (Nat.le_succ _)
  have both := big.mono fun i bi => two_finite bi (hk i) (D i) (E i)
  refine ⟨critical_growth n k 1 (by decide) hn whole rate,critical_growth n k (2^128) (by decide) hn whole rate,
    ?_,both.mono (fun i h => h.2),by linarith⟩
  have sl := rate.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  have lim : Tendsto (fun i => 1-((k i:ℝ)+1)/n i) atTop (𝓝 (1-ρ)) := by
    simpa [add_div] using (tendsto_const_nhds (x:=(1:ℝ))).sub sl
  exact lim.congr' (both.mono fun i h => h.1.symm)

#print axioms has_domain
#print axioms critical_growth
#print axioms two_finite
#print axioms critical_nonuniqueness
end ProximityGap.PrimeFieldCriticalEntropy
