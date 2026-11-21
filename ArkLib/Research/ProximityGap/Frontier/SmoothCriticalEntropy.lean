/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothFermatCapacity
import ArkLib.Research.ProximityGap.Frontier.PrimeFieldEntropyPhase
import Mathlib.Topology.Sequences

/-! # A two-dimension critical transition on the same smooth domain -/
set_option autoImplicit false
namespace ProximityGap.SmoothCriticalEntropy
open Filter Topology Finset ReedSolomon PrimeFieldCapacityWindow PrimeFieldEntropyPhase SmoothFermatCapacity
open scoped NNReal ENNReal

private theorem small_binomial (t r : ℕ) (hr : r≤16*t) : (16*t).choose r ≤ 2^(t+5*r) := by
  let n := 16*t
  have total := add_pow (1:ℕ) 32 n
  norm_num only [Nat.reduceAdd] at total
  have term : 32^(n-r)*n.choose r ≤ 33^n := by
    rw [total]
    simpa using (single_le_sum (f:=fun j => (1:ℕ)^j*32^(n-j)*n.choose j)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (by omega : r<n+1)))
  have bound : 33^n ≤ 2^t*32^n := by
    dsimp [n]
    rw [pow_mul,pow_mul,← mul_pow]
    exact Nat.pow_le_pow_left (by decide) t
  have h := Nat.mul_le_mul_left (32^r) (term.trans bound)
  have eq : 32^r*32^(n-r)=32^n := by rw [← pow_add,Nat.add_sub_cancel' hr]
  rw [← Nat.mul_assoc,eq] at h
  have h2 : 32^n*n.choose r ≤ 32^n*(2^t*32^r) := by convert h using 1; ring
  have cap := Nat.le_of_mul_le_mul_left h2 (by positivity)
  simpa only [pow_add,pow_mul,show (2:ℕ)^5=32 by decide] using cap

private theorem next_le (n a : ℕ) (ha : n≤256*(a+1)) : n.choose (a+1)≤256*n.choose a := by
  apply Nat.le_of_mul_le_mul_right (c:=a+1) _ (by omega)
  rw [Nat.choose_succ_right_eq]
  calc n.choose a*(n-a)≤n.choose a*(256*(a+1)) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

/-- `a` is the last index whose detecting circuits fit the full security budget.
The next two binomial ratios are bounded on the designated interval. -/
theorem crossing {t p : ℕ} (ht : 2^20≤t) (lo : 2^(2*t)<p) (hi : p≤2^(4*t)) :
    ∃ a : ℕ, t/16≤a ∧ a<t ∧ (16*t).choose a*2^128≤p ∧
      p≤(2^128*256)*(16*t).choose a ∧
      (16*t).choose (a+2)/(a+2)≤p/2^128 ∧ p≤(2^128-1)*(16*t).choose (a+2) := by
  let n := 16*t
  let S := (range (t+1)).filter fun j => n.choose j*2^128≤p
  have start : t/16∈S := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega),?_⟩
    have h := Nat.mul_le_mul_right (2^128) (small_binomial t (t/16) (by omega))
    rw [← pow_add] at h
    exact h.trans ((Nat.pow_le_pow_right (by decide : 1≤2) (show t+5*(t/16)+128≤2*t by omega)).trans lo.le)
  let a := S.max' ⟨_,start⟩
  have ma : a∈S := max'_mem ..
  have good := (mem_filter.mp ma).2
  have atMost := mem_range.mp (mem_filter.mp ma).1
  have first : t/16≤a := le_max' S _ start
  have at' : a<t := by
    by_contra! h
    have eq : a=t := by omega
    have many := block_choices 16 t
    rw [show 16=2^4 by decide,← pow_mul] at many
    change (16*t).choose a*2^128 ≤ p at good
    rw [eq] at good
    have nn := Nat.choose_pos (show t≤16*t by omega)
    change 2^(4*t)≤(16*t).choose t at many
    have pB := hi.trans many
    omega
  have ng : p<n.choose (a+1)*2^128 := by
    by_contra! h
    have m : a+1∈S := mem_filter.mpr ⟨mem_range.mpr (by omega),h⟩
    have tooBig : a+1≤a := le_max' S _ m
    omega
  have n1 := next_le n a (by dsimp [n]; omega)
  have n2 := next_le n (a+1) (by dsimp [n]; omega)
  have more : 2*n.choose (a+1)≤n.choose (a+2) := by
    apply Nat.le_of_mul_le_mul_right (c:=a+2) _ (by omega)
    rw [Nat.choose_succ_right_eq n (a+1)]
    calc 2*n.choose (a+1)*(a+2)=n.choose (a+1)*(2*(a+2)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by dsimp [n];omega)
  refine ⟨a,first,at',good,?_,?_,?_⟩
  · calc p ≤ n.choose (a+1)*2^128 := ng.le
         _ ≤ (256*n.choose a)*2^128 := Nat.mul_le_mul_right _ n1
         _ = _ := by dsimp [n];ring
  · apply (Nat.div_le_of_le_mul (show n.choose (a+2)≤(a+2)*n.choose a by
      calc n.choose (a+2)≤256*(256*n.choose a) := n2.trans (Nat.mul_le_mul_left _ n1)
           _ = 65536*n.choose a := by ring
           _ ≤ _ := Nat.mul_le_mul_right _ (by omega))).trans
    exact (Nat.le_div_iff_mul_le (by decide)).mpr good
  · change p≤(2^128-1)*n.choose (a+2)
    omega

/-- An exact one-versus-predecessor transition at two message dimensions
separated by two, on every embedding in this field-size window. -/
theorem adjacent_radii {t p : ℕ} [Fact p.Prime] (ht : 2^20≤t)
    (lo : 2^(2*t)<p) (hi : p≤2^(4*t)) :
    ∃ a : ℕ, t/16≤a ∧ a<t ∧ (16*t).choose a≤p ∧ p≤(2^128*256)*(16*t).choose a ∧
      ∀ D : Fin (16*t) ↪ ZMod p,
        radius D (a-1)=1 ∧ radius D (a+1)=1-((a:ℝ)+2)/(16*t:ℕ) := by
  obtain ⟨a,al,au,base,ub,bu,bl⟩ := crossing ht lo hi
  have hk : a-1+1=a := by omega
  have lo' : (16*t).choose a≤p := (Nat.le_mul_of_pos_right _ (by decide)).trans base
  refine ⟨a,al,au,lo',ub,?_⟩
  intro D
  let _ : NeZero (16*t) := ⟨by omega⟩
  let _ : SampleableType (ZMod p) := SampleableType.ofFintype _
  refine ⟨radius_one D (by omega) (by simpa only [hk] using base),?_⟩
  have cert := CircuitBudgetRadius.wide_deltaStar (k:=a+1) (D:=2^128) D (by omega) (by omega) (by decide)
    (by simpa using bu) (by simpa using bl)
  have hn : 0<((16*t:ℕ):ℝ≥0) := by exact_mod_cast (show 0<16*t by omega)
  have le : ((a+1+1:ℕ):ℝ≥0)/(16*t:ℕ)≤1 := (div_le_one hn).mpr (by exact_mod_cast (show a+2≤16*t by omega))
  unfold radius
  simp only [Nat.cast_pow,Nat.cast_ofNat] at cert
  rw [cert,NNReal.coe_sub le]
  push_cast
  ring

/-- The fixed finite shift ensures every index lies in the certified window. -/
def block (i : ℕ) := 16*scale (i+2^20)

def fieldSize (i : ℕ) := primeAt (i+2^20)
instance fieldSize_prime (i : ℕ) : Fact (fieldSize i).Prime := primeFact (i+2^20)

set_option maxRecDepth 4096 in
/-- Along a common subsequence of the explicit smooth fields, two dimensions
differing by two have the very same nontrivial limiting rate and critical
field exponent. The radii are exactly one at the lower dimension and tend
to one minus the rate at the higher dimension. -/
theorem smooth_critical : ∃ (σ a : ℕ → ℕ) (ρ : ℝ), StrictMono σ ∧ 1/512≤ρ ∧ ρ<1/16 ∧
    Tendsto (fun i => block (σ i)) atTop atTop ∧
    Tendsto (fun i => ((a i-1:ℕ):ℝ)/block (σ i)) atTop (𝓝 ρ) ∧
    Tendsto (fun i => ((a i+1:ℕ):ℝ)/block (σ i)) atTop (𝓝 ρ) ∧
    Tendsto (fun i => Real.log (fieldSize (σ i))/block (σ i)) atTop (𝓝 (Real.binEntropy ρ)) ∧
    ∃ D : ∀ i, Fin (block (σ i)) ↪ ZMod (fieldSize (σ i)),
      (∀ i, Nonempty (ReedSolomon.Smooth (D i))) ∧
      (∀ i, radius (D i) (a i-1)=1 ∧ radius (D i) (a i+1)=1-((a i:ℝ)+2)/block (σ i)) ∧
      Tendsto (fun i => radius (D i) (a i+1)) atTop (𝓝 (1-ρ)) := by
  classical
  let t := fun i => scale (i+2^20)
  have large (i : ℕ) : i+2^20<t i := (parameters _).1
  have positive (i : ℕ) : 0<t i := by have := large i; omega
  have top : Tendsto block atTop atTop := tendsto_atTop_mono (fun i => by
    change i≤16*t i; have := large i; omega) tendsto_id
  have cert (i : ℕ) := adjacent_radii (p:=fieldSize i) (t:=t i)
    (by have := large i; omega) (parameters _).2.2.1 (parameters _).2.2.2
  choose a left right count_le prime_le branch using cert
  let x := fun i => (a i:ℝ)/block i
  have box (i : ℕ) : x i ∈ Set.Icc (1/512:ℝ) (1/16) := by
    have ti := large i
    have ll := left i
    have rr := right i
    have npos : 0<(block i:ℝ) := by exact_mod_cast (show 0<16*t i by omega)
    constructor
    · apply (le_div_iff₀ npos).mpr
      have nn : 16*t i≤512*a i := by omega
      have nc : (block i:ℝ)≤512*(a i:ℝ) := by exact_mod_cast nn
      linarith
    · apply (div_le_iff₀ npos).mpr
      have nn : 16*a i≤16*t i := by omega
      have nc : 16*(a i:ℝ)≤(block i:ℝ) := by exact_mod_cast nn
      linarith
  obtain ⟨ρ,hr,σ,strict,hx⟩ := isCompact_Icc.tendsto_subseq box
  have nlim : Tendsto (fun i => block (σ i)) atTop atTop := top.comp strict.tendsto_atTop
  have unit := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp nlim
  have val : Tendsto (fun i => (a (σ i):ℝ)/block (σ i)) atTop (𝓝 ρ) := hx
  have amin (i : ℕ) : 1≤a i := by have := left i; have := large i; omega
  have pr (i : ℕ) : a i<block i := by change a i<16*t i;have := right i;omega
  have subrate : Tendsto (fun i => ((a (σ i)-1:ℕ):ℝ)/block (σ i)) atTop (𝓝 ρ) := by
    simpa only [Function.comp_apply,Nat.cast_sub (amin _),Nat.cast_one,sub_div,sub_zero] using val.sub unit
  have addrate : Tendsto (fun i => ((a (σ i)+1:ℕ):ℝ)/block (σ i)) atTop (𝓝 ρ) := by
    simpa only [Function.comp_apply,Nat.cast_add,Nat.cast_one,add_div,add_zero] using val.add unit
  have binom := choose_log_tendsto (fun i => block (σ i)) (fun i => a (σ i)) nlim
    (Eventually.of_forall fun i => ⟨amin _,pr _⟩) val
  let K : ℝ := 2^128*256
  have correction := unit.const_mul (Real.log K)
  rw [mul_zero] at correction
  have limUp := binom.add correction
  rw [add_zero] at limUp
  have loglim : Tendsto (fun i => Real.log (fieldSize (σ i))/block (σ i)) atTop (𝓝 (Real.binEntropy ρ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' binom limUp
    · apply Eventually.of_forall
      intro i
      have cp := Nat.choose_pos (pr (σ i)).le
      exact div_le_div_of_nonneg_right (Real.log_le_log (by exact_mod_cast cp) (by exact_mod_cast count_le (σ i))) (by positivity)
    · apply Eventually.of_forall
      intro i
      let N := (block (σ i)).choose (a (σ i))
      have cp : 0<(N:ℝ) := by exact_mod_cast Nat.choose_pos (pr (σ i)).le
      have kp : 0<K := by dsimp [K]; positivity
      have pp : 0<(fieldSize (σ i):ℝ) := by exact_mod_cast (primeFact _).out.pos
      have up : (fieldSize (σ i):ℝ)≤K*N := by dsimp [K,N];exact_mod_cast prime_le (σ i)
      have lg := Real.log_le_log pp up
      rw [Real.log_mul kp.ne' cp.ne'] at lg
      have r := div_le_div_of_nonneg_right lg (Nat.cast_nonneg (block (σ i)) : 0≤(block (σ i):ℝ))
      change Real.log (fieldSize (σ i))/block (σ i) ≤ Real.log (N:ℝ)/block (σ i)+Real.log K*(1/block (σ i))
      rw [add_div,add_comm] at r
      simpa only [one_div,div_eq_mul_inv,one_mul] using r
  have cap : Real.binEntropy ρ≤Real.log 2/4 := by
    apply le_of_tendsto_of_tendsto loglim tendsto_const_nhds
    apply Eventually.of_forall
    intro i
    have hh := (parameters (σ i+2^20)).2.2.2
    have pp : 0<(fieldSize (σ i):ℝ) := by exact_mod_cast (primeFact _).out.pos
    have ll := Real.log_le_log pp (show (fieldSize (σ i):ℝ)≤(2:ℝ)^(4*t (σ i)) by exact_mod_cast hh)
    rw [Real.log_pow] at ll
    have npos : 0<(block (σ i):ℝ) := by exact_mod_cast (show 0<16*t (σ i) by have := positive (σ i);omega)
    apply (div_le_iff₀ npos).mpr
    change Real.log (fieldSize (σ i)) ≤ Real.log 2/4*((16*t (σ i):ℕ):ℝ)
    push_cast at ll ⊢
    linarith
  have rlt : ρ<1/16 := by
    apply lt_of_le_of_ne hr.2
    intro eq
    rw [eq] at cap
    have l16 : Real.log (16:ℝ)=4*Real.log 2 := by
      rw [show (16:ℝ)=2^4 by norm_num,Real.log_pow];norm_num
    have pos := Real.log_pos (show (1:ℝ)<16/15 by norm_num)
    unfold Real.binEntropy at cap
    rw [show ((1:ℝ)/16)⁻¹=16 by norm_num,show (1:ℝ)-1/16=15/16 by norm_num,
      show ((15:ℝ)/16)⁻¹=16/15 by norm_num,l16] at cap
    linarith
  refine ⟨σ,fun i => a (σ i),ρ,strict,hr.1,rlt,nlim,subrate,addrate,loglim,?_⟩
  have sm (i : ℕ) : ∃ D : Fin (block (σ i)) ↪ ZMod (fieldSize (σ i)), Nonempty (ReedSolomon.Smooth D) := by
    unfold block fieldSize
    exact smooth (σ i+2^20)
  choose D hs using sm
  refine ⟨D,hs,fun i => branch (σ i) (D i),?_⟩
  have twice := unit.const_mul (2:ℝ)
  rw [mul_zero] at twice
  have rr := (tendsto_const_nhds (x:=(1:ℝ))).sub (val.add twice)
  rw [add_zero] at rr
  apply rr.congr'
  apply Eventually.of_forall
  intro i
  change 1-((a (σ i):ℝ)/block (σ i)+2*(1/block (σ i)))=radius (D i) (a (σ i)+1)
  calc _ = 1-((a (σ i):ℝ)+2)/block (σ i) := by rw [add_div,mul_one_div]
       _ = _ := (branch (σ i) (D i)).2.symm

#print axioms smooth_critical

#print axioms crossing
#print axioms adjacent_radii
end ProximityGap.SmoothCriticalEntropy
