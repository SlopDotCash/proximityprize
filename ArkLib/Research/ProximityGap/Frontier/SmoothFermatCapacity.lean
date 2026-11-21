/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldCapacityWindow
import ArkLib.Research.ProximityGap.Frontier.SmoothPowerMcaDescent
import Mathlib.NumberTheory.Fermat
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Analysis.SpecificLimits.Normed

/-! # An unbounded smooth prime-field family attaining asymptotic MCA capacity -/
set_option autoImplicit false
namespace ProximityGap.SmoothFermatCapacity
open Filter Topology PrimeFieldCapacityWindow

def primeAt (i : ℕ) := (Nat.fermatNumber (4*i+4)).minFac
instance primeFact (i : ℕ) : Fact (primeAt i).Prime := ⟨Nat.minFac_prime (Nat.fermatNumber_ne_one _)⟩

/-- The scale `t` used in a length `16*t` smooth subgroup. -/
def scale (i : ℕ) := 2^(Nat.clog 2 (Nat.clog 2 (primeAt i))-2)

/-- Explicit simultaneous arithmetic window. No choice or distribution theorem for
primes is needed: the field is the least prime factor of the indicated Fermat number. -/
theorem parameters (i : ℕ) : i<scale i ∧ 16*scale i ∣ primeAt i-1 ∧
    2^(2*scale i)<primeAt i ∧ primeAt i≤2^(4*scale i) := by
  let j := 4*i+4
  let p := primeAt i
  let l := Nat.clog 2 p
  let b := Nat.clog 2 l
  have jp : 4≤j := by dsimp [j]; omega
  have hd : p ∣ Nat.fermatNumber j := Nat.minFac_dvd _
  have hp : p.Prime := (primeFact i).out
  obtain ⟨c,pc⟩ := Nat.fermat_primeFactors_one_lt j p (by omega) hp hd
  have cp : 0<c := by by_contra! hc; have := hp.two_le; simp [show c=0 by omega] at pc; omega
  have low : 2^(j+2)<p := by rw [pc]; have := Nat.le_mul_of_pos_left (2^(j+2)) cp; omega
  have lj : j+2<l := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr low
  have lb : l≤2^b := Nat.le_pow_clog (by decide) _
  have bb : 2≤b := by
    by_contra! hb
    have le := Nat.pow_le_pow_right (by decide : 1≤2) (show b≤1 by omega)
    omega
  have sc : 4*scale i=2^b := by
    change 2^2*2^(b-2)=_
    rw [← pow_add,show 2+(b-2)=b by omega]
  have half : 2*scale i=2^b.pred := by
    change 2^1*2^(b-2)=_
    rw [← pow_add,show 1+(b-2)=b.pred by rw [Nat.pred_eq_sub_one];omega]
  have len : 16*scale i=2^(b+2) := by rw [pow_add,← sc]; ring
  have high : p≤Nat.fermatNumber j := Nat.le_of_dvd (by have := Nat.three_le_fermatNumber j; omega) hd
  refine ⟨by dsimp [j] at lj; omega,?_,?_,?_⟩
  · rw [len]
    by_cases full : p=Nat.fermatNumber j
    · change _ ∣ p-1
      rw [full,Nat.fermatNumber,Nat.add_sub_cancel]
      apply pow_dvd_pow
      have ep : p≤2^(2^(j+1)) := by
        rw [full,Nat.fermatNumber,pow_succ 2 j, Nat.mul_two,pow_add 2 (2^j) (2^j)]
        have pos : 1 < 2^(2^j) := Nat.one_lt_pow (by positivity) (by decide)
        nlinarith
      have jb : b≤j+1 := Nat.clog_le_of_le_pow (Nat.clog_le_of_le_pow ep)
      have grow : ∀ t : ℕ, t+7≤2^(t+4) := by
        intro t
        induction t with
        | zero => decide
        | succ t ih => rw [show t+1+4=(t+4)+1 by omega,pow_succ]; omega
      have edge := grow (j-4)
      rw [show j-4+4=j by omega] at edge
      omega
    · have less : p≤2^(2^j) := by
        rw [Nat.fermatNumber] at high full
        omega
      have jb : b≤j := Nat.clog_le_of_le_pow (Nat.clog_le_of_le_pow less)
      apply (pow_dvd_pow 2 (show b+2≤j+2 by omega)).trans
      change 2^(j+2)∣p-1
      rw [pc,Nat.add_sub_cancel]
      exact dvd_mul_left _ _
  · rw [half]
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp
      (Nat.pow_pred_clog_lt_self (b:=2) (by decide) (by omega : 1<l))
  · rw [sc]
    apply (Nat.le_pow_clog (b:=2) (by decide) p).trans
    exact Nat.pow_le_pow_right (by decide) lb

/-- This actual length is dyadic. -/
theorem dyadic (i : ℕ) : ∃ a : ℕ, 16*scale i=2^a := by
  refine ⟨4+(Nat.clog 2 (Nat.clog 2 (primeAt i))-2),?_⟩
  rw [pow_add]; rfl

/-- Every field in the explicit sequence contains a smooth domain of length `16*scale i`. -/
theorem smooth (i : ℕ) : ∃ D : Fin (16*scale i) ↪ ZMod (primeAt i), Nonempty (ReedSolomon.Smooth D) :=
  SmoothPowerMcaDescent.exists_prime_domain (parameters i).2.1 (dyadic i)

/-- Choosing one entry from each block of size `h` gives `h^t` distinct `t`-subsets. -/
theorem block_choices (h t : ℕ) : h^t ≤ (h*t).choose t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ,Nat.mul_succ,Nat.add_choose_eq]
    apply (Nat.mul_le_mul_right h ih).trans
    simpa using (Finset.single_le_sum (s:=Finset.HasAntidiagonal.antidiagonal (t+1))
      (f:=fun z : ℕ×ℕ => (h*t).choose z.1*h.choose z.2) (fun _ _ => Nat.zero_le _)
      (show (t,1)∈Finset.HasAntidiagonal.antidiagonal (t+1) by simp))

private theorem choices (t b : ℕ) (ht : 0<t) (lo : t≤b+1) (hi : b+1≤16*t-t) :
    2^(4*t) ≤ (16*t).choose (b+1) := by
  have inc {a d : ℕ} (h1 : a≤d) (h2 : d≤(16*t)/2) : (16*t).choose a≤(16*t).choose d := by
    induction d, h1 using Nat.le_induction with
    | base => rfl
    | succ d ha ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have start := block_choices 16 t
  rw [show 16=2^4 by decide,← pow_mul] at start
  by_cases le : b+1≤(16*t)/2
  · exact start.trans (inc lo le)
  · rw [← Nat.choose_symm (n:=16*t) (k:=b+1) (by omega)]
    exact start.trans (inc (by omega) (by omega))

private theorem scale_grows : Tendsto scale atTop atTop :=
  tendsto_atTop_mono (fun i => (parameters i).1.le) tendsto_id

/-- On these actual fields the capacity-gap limit holds uniformly for varying
rates throughout the indicated band, independently of domain or smoothness. -/
theorem gap (D : ∀ i, Fin (16*scale i) ↪ ZMod (primeAt i)) (k : ℕ → ℕ)
    (band : ∀ᶠ i in atTop, scale i≤k i ∧ k i+1≤15*scale i) :
    Tendsto (fun i => 1-(k i:ℝ)/(16*scale i:ℕ)-radius (D i) (k i)) atTop (𝓝 0) := by
  have growing : Tendsto (fun i => 16*scale i) atTop atTop :=
    tendsto_atTop_mono (fun i => Nat.le_mul_of_pos_left _ (by decide : 0<16)) scale_grows
  have pos (i : ℕ) : 0<scale i := (Nat.zero_le i).trans_lt (parameters i).1
  apply capacity_gap_tendsto_of_binomial primeAt (fun i => 16*scale i) k D growing
  · exact band.mono fun i hi => by have := pos i; omega
  · intro d
    have lim := (tendsto_pow_const_div_const_pow_of_one_lt d (by norm_num : (1:ℝ)<4)).comp scale_grows
    have sm := lim.eventually_lt_const (show (0:ℝ)<(1/(16:ℝ)^d) by positivity)
    filter_upwards [sm] with i h
    change (scale i:ℝ)^d/(4:ℝ)^(scale i)<1/(16:ℝ)^d at h
    have z := (div_lt_div_iff₀ (by positivity : 0<(4:ℝ)^scale i) (by positivity : 0<(16:ℝ)^d)).mp h
    have nn : (16*scale i)^d < (4:ℕ)^scale i := by
      rw [mul_pow,mul_comm]; simp only [one_mul] at z; exact_mod_cast z
    have pow : (4:ℕ)^scale i = 2^(2*scale i) := by rw [pow_mul]; rfl
    rw [pow] at nn
    exact nn.le.trans (parameters i).2.2.1.le
  · apply band.mono
    intro i hi
    have b := choices (scale i) (k i) (pos i) (by omega) (by omega)
    exact ((parameters i).2.2.2.trans b).trans (Nat.le_mul_of_pos_left _ (by decide))

/-- Any sequence of the prescribed prime-field domains, smooth or otherwise,
attains asymptotic capacity simultaneously for all four standard rates. A
factor `s=1,2,4,8` gives rate `s/16`. -/
theorem rates (D : ∀ i, Fin (16*scale i) ↪ ZMod (primeAt i)) (s : ℕ) (hs : 1 ≤ s) (hu : s ≤ 14) :
    Tendsto (fun i => radius (D i) (s*scale i)) atTop (𝓝 (1-(s:ℝ)/16)) := by
  have pos (i : ℕ) : 0<scale i := (Nat.zero_le i).trans_lt (parameters i).1
  have h := gap D (fun i => s*scale i) (Eventually.of_forall fun i => by
    have h1 := Nat.le_mul_of_pos_left (scale i) (by omega : 0<s)
    have h2 := Nat.mul_le_mul_right (scale i) hu
    have := pos i
    omega)
  have rate : Tendsto (fun i => (((s*scale i:ℕ):ℝ)/((16*scale i:ℕ):ℝ))) atTop (𝓝 ((s:ℝ)/16)) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun i => by
      change (s:ℝ)/16=(((s*scale i:ℕ):ℝ)/((16*scale i:ℕ):ℝ))
      have nonzero : (scale i:ℝ)≠0 := by exact_mod_cast (pos i).ne'
      push_cast
      field_simp

  have both := ((tendsto_const_nhds (x:=(1:ℝ))).sub rate).sub h
  simpa only [Pi.sub_apply,sub_sub_cancel,sub_zero] using both

/-- The sequence can be realized by a single choice of smooth domains across
all four limits. -/
theorem smooth_rates : ∃ D : ∀ i, Fin (16*scale i) ↪ ZMod (primeAt i),
    (∀ i, Nonempty (ReedSolomon.Smooth (D i))) ∧
    ∀ s : ℕ, 1 ≤ s → s ≤ 14 → Tendsto (fun i => radius (D i) (s*scale i)) atTop (𝓝 (1-(s:ℝ)/16)) := by
  choose D hs using smooth
  exact ⟨D,hs,rates D⟩

#print axioms parameters
#print axioms smooth
#print axioms gap
#print axioms rates
#print axioms smooth_rates
end ProximityGap.SmoothFermatCapacity
