/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralTwoLineArithmetic
import ArkLib.Research.ProximityGap.Frontier.TwoHeadLinearBudget
import ArkLib.Research.ProximityGap.Frontier.GeneralTwoLineSafety
import ArkLib.Research.ProximityGap.Frontier.GeneralOverlapPacking

/-! # The half-budget phase past the half-distance plateau
The predecessor consists of two fewer available challenges than the failing
step. A two-line count and a matching distinct-label construction decide
the exact finite threshold along prescribed domain sequences.
-/
set_option autoImplicit false
namespace ProximityGap.LinearFieldTwoLinePhase
open Filter Topology MCAThresholdLedger GeneralTwoLineArithmetic
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

/-- A two-line good predecessor and the two-head witness identify the
supremum boundary, including odd integer scalar budgets. -/
private theorem finite {p n k Q j : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (Qpos : 0<Q) (index : j=p/Q/2) (jpos : 0<j)
    (good : epsMCA (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p))
      (((j-1:ℕ):ℝ≥0)/n) ≤ ((2*(j-1)+2:ℕ):ℝ≥0∞)/p)
    (failure : ((2*(j+1):ℕ):ℝ≥0∞)/p ≤ epsMCA (F:=ZMod p)
      (ReedSolomon.code x k : Set (Fin n → ZMod p)) ((j:ℝ≥0)/n)) (jn : j≤n) :
    mcaDeltaStar (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p)) (1/(Q:ℝ≥0∞)) =
      (j:ℝ≥0)/n := by
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    apply lt_of_lt_of_le _ failure
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos Qpos]
    omega
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good jpos jn
    apply le_trans good
    rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=p.Prime)).pos Qpos]
    omega

/-- At normalized budget twice a, strictly beyond the half-distance plateau,
the operational radius is eventually exactly the integer half-budget index
divided by n throughout this two-line incidence range. -/
theorem exact_threshold (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ) (two : 2≤Q)
    (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (a_eq : a=slope/Q/2) (ha : 0<a) (core : ρ+a<1)
    (right : 1<ρ+(a+a)) (moment : ρ<(1-a)^3) (geom : 1+3*ρ<3*(1-a)) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) =
      ((p i/Q/2:ℕ):ℝ≥0)/n i := by
  have hQ : 0<Q := by omega
  let j i := p i/Q/2
  have jl : Tendsto (fun i => (j i:ℝ)/n i) atTop (𝓝 a) := by
    rw [a_eq]
    exact LinearFieldBudgetLimit.floor_limit _ n 2 (by decide) hn
      (LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf)
  have down := previous_limit j n hn ha jl
  have a1 : a<1 := by linarith
  obtain ⟨L,L2,event⟩ := eventually_hypotheses n k (fun i => j i-1) hn ha a1 down rate moment geom
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have je := jl.add tiny
  have qr : (0:ℝ)<Q := by exact_mod_cast hQ
  have twoR : (2:ℝ)≤Q := by exact_mod_cast two
  have val : (a*2)*(Q:ℝ)=slope := by rw [a_eq]; field_simp
  have fieldMargin : 4*a < slope+1 := by nlinarith [mul_nonneg (by linarith : 0≤2*a) (sub_nonneg.mpr twoR)]
  have large := (je.const_mul 4).eventually_lt (hf.add_const 1) (by simpa using fieldMargin)
  have cap := (rate.add je).eventually_lt_const (by simpa using core)
  have deg := (rate.add (jl.add jl)).eventually_const_lt right
  have jp := jl.eventually_const_lt ha
  have kp := tiny.eventually_lt rate positive
  filter_upwards [event,large,cap,deg,jp,kp] with i arithmetic large cap deg jp kp
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 4*((j i:ℝ)/n i+1/n i)<(p i:ℝ)/n i+1 at large
  field_simp at large
  change (k i:ℝ)/n i+((j i:ℝ)/n i+1/n i)<1 at cap
  change 1 < (k i:ℝ)/n i+((j i:ℝ)/n i+(j i:ℝ)/n i) at deg
  simp only [←add_div,div_lt_one ni,one_lt_div ni] at cap deg
  have jj : 0<j i := by exact_mod_cast (div_pos_iff_of_pos_right ni).mp jp
  change 1/(n i:ℝ)<(k i:ℝ)/n i at kp
  have kk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp kp
  have supply : 4*(j i+1) ≤ p i+n i := by exact_mod_cast
    (show 4*((j i:ℝ)+1)≤(p i:ℝ)+n i by linarith)
  have cr : k i+j i+1≤n i := by exact_mod_cast (show (k i:ℝ)+j i+1≤n i by linarith)
  have dr : Fintype.card (Fin (n i))≤k i+2*j i := by
    rw [Fintype.card_fin];exact_mod_cast (show (n i:ℝ)≤k i+2*j i by linarith)
  have hi : ((2*(j i+1):ℕ):ℝ≥0∞)/(p i) ≤ epsMCA (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) ((j i:ℝ≥0)/n i) := by
    by_cases pr : 2*(j i+1) ≤ n i
    · simpa only [Fintype.card_fin,ZMod.card] using TwoHeadLinearBudget.errors (x i)
        (by simpa using pr) dr (by simpa using cr)
    · simpa only [Fintype.card_fin,ZMod.card] using
        ArkLib.ProximityGap.Frontier.GeneralOverlapPacking.errors (x i) (k i) (j i) kk
          (by rw [Fintype.card_fin];omega) (by rw [Fintype.card_fin];omega)
          (by rw [Fintype.card_fin,ZMod.card];omega)
  let e := j i-1
  have en : e≤n i := arithmetic.1
  have threshold : ⌈(1-(e:ℝ≥0)/n i)*(Fintype.card (Fin (n i)):ℝ≥0)⌉₊=n i-e := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),
      ←Nat.cast_tsub,Nat.ceil_natCast]
  have bound := GeneralTwoLineSafety.epsMCA_le (x i) ((e:ℝ≥0)/n i) (Fintype.card_fin _)
    (show e+(n i-e)=n i by omega) (by omega : 1≤k i) (show k i≤n i-e by dsimp [e];omega)
    L2 threshold arithmetic.2.1 arithmetic.2.2
  rw [ZMod.card] at bound
  exact finite (j:=j i) (k:=k i) (x i) hQ rfl jj bound hi (Nat.le_of_add_left_le (by omega : k i + j i ≤ n i))

/-- The corresponding limiting radius is exactly half the normalized field budget. -/
theorem limit (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ) (two : 2≤Q)
    (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (a_eq : a=slope/Q/2) (ha : 0<a) (core : ρ+a<1)
    (right : 1<ρ+(a+a)) (moment : ρ<(1-a)^3) (geom : 1+3*ρ<3*(1-a)) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i)) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) : ℝ)) atTop (𝓝 a) := by
  have eq := exact_threshold p n k x Q two hn hf rate positive a_eq ha core right moment geom
  have result := LinearFieldBudgetLimit.floor_limit _ n 2 (by decide) hn
    (LinearFieldBudgetLimit.floor_limit p n Q (by omega : 0<Q) hn hf)
  change Tendsto _ atTop (𝓝 (slope/(Q:ℝ)/2)) at result
  rw [←a_eq] at result
  apply result.congr'
  filter_upwards [eq] with i hi
  rw [hi]
  simp

/-- A length-uniform finite window. At every length at least 4096 and
dimension at most one eighth of the length, the first failing index is
the half-budget j whenever (n-k)/2 ≤ j ≤ 31n/64. -/
theorem finite_low_rate {p n k Q : ℕ} [Fact p.Prime] [NeZero n] (x : Fin n ↪ ZMod p)
    (Qpos : 0<Q) (length : 4096≤n) (hk : 2≤k) (rate : 8*k≤n)
    (left : n≤k+2*(p/Q/2)) (right : 64*(p/Q/2)≤31*n) :
    mcaDeltaStar (F:=ZMod p) (ReedSolomon.code x k : Set (Fin n → ZMod p)) (1/(Q:ℝ≥0∞)) =
      ((p/Q/2:ℕ):ℝ≥0)/n := by
  let j := p/Q/2
  change n≤k+2*j at left
  change 64*j≤31*n at right
  let e := j-1
  let t := n-e
  have jp : 0<j := by omega
  have en : e+t=n := by dsimp [t,e]; omega
  have tmin : 33*n≤64*t := by omega
  have low : 1792≤e+2 := by dsimp [e];omega
  have cubic : (e+2)*k*n^2+(16+2)*n^3<(e+2)*t^3 := by
    have a := Nat.mul_le_mul_left (e+2) (Nat.pow_le_pow_left tmin 3)
    have b := Nat.mul_le_mul_left ((e+2)*n^2) rate
    have c := Nat.mul_le_mul_right (n^3) low
    have d : 0<n^3 := pow_pos (by omega) _
    nlinarith only [a,b,c,d]
  have geometry : (n+3*k)*16+2*n < 3*t*16 := by omega
  have ni : (n:ℝ≥0)≠0 := by exact_mod_cast NeZero.ne n
  have hceil : ⌈(1-(e:ℝ≥0)/n)*(Fintype.card (Fin n):ℝ≥0)⌉₊=t := by
    rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ ni,←Nat.cast_tsub,Nat.ceil_natCast]
  have bound := GeneralTwoLineSafety.epsMCA_le x ((e:ℝ≥0)/n) (Fintype.card_fin _) en
    (by omega : 1≤k) (by omega : k≤t) (by decide : 2≤16) hceil cubic geometry
  have fail := TwoHeadLinearBudget.errors (k:=k) (e:=j) x (by rw [Fintype.card_fin];omega)
    (by rwa [Fintype.card_fin]) (by rw [Fintype.card_fin];omega)
  rw [ZMod.card] at bound
  rw [ZMod.card,Fintype.card_fin] at fail
  exact finite (k:=k) (j:=j) x Qpos rfl jp bound fail (by omega)

end ProximityGap.LinearFieldTwoLinePhase
#print axioms ProximityGap.LinearFieldTwoLinePhase.exact_threshold
#print axioms ProximityGap.LinearFieldTwoLinePhase.limit
#print axioms ProximityGap.LinearFieldTwoLinePhase.finite_low_rate
