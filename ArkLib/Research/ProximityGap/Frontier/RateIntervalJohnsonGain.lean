/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity

/-! # A one-percent finite Johnson improvement throughout a rate interval

A fixed first-order interpolation profile gives an affine sufficient inequality
in length, dimension and agreement. Four such inequalities cover the full
interval from one sixteenth through one half. They apply to every length of
at least 4096 and to every prescribed prime-field domain.
-/
namespace ProximityGap.RateIntervalJohnsonGain
open Finset ReedSolomon ReedSolomon.HiddenDerivative CoreDefinitions FineGridFirstOrderSecurity

private structure Profile where
  m : ℕ
  M : ℕ
  v : ℕ
  h : ℕ
  rows : ℕ
  moment : ℕ
  columns : ℕ
  left : ℕ
  right : ℕ

private def prof : Fin 4 → Profile
  | 0 => ⟨12,6,36,672,256746,3000634,1866564,747,1125⟩
  | 1 => ⟨16,7,33,320,244296,1322636,1182272,1125,1500⟩
  | 2 => ⟨24,9,39,368,789025,2629060,2959560,1500,1875⟩
  | 3 => ⟨40,12,55,1024,8251334,19488326,25860640,1875,2125⟩

private def weight (c : Profile) (t : ℕ) : ℕ := (min t c.M+1)*(c.h+1-t)

private theorem coefficients (i : Fin 4) : let c := prof i
    rowSlots 1 c.m c.M c.v c.h=c.rows ∧
    (∑ t ∈ range (c.v+1), t*weight c t)=c.moment ∧
    c.m*(∑ t ∈ range (c.v+1), weight c t)=c.columns := by
  fin_cases i <;> decide

private theorem slots_of_affine (i : Fin 4) (n k A : ℕ) (ha :
    (prof i).rows*n+(prof i).moment*k < (prof i).columns*A) :
    rowSlots n (prof i).m (prof i).M (prof i).v (prof i).h <
      columnSlots k A (prof i).m (prof i).M (prof i).v (prof i).h := by
  let c := prof i
  have cf := coefficients i
  change rowSlots 1 c.m c.M c.v c.h=c.rows ∧ _ at cf
  have row : rowSlots n c.m c.M c.v c.h = c.rows*n := by
    rw [←cf.1]
    unfold rowSlots
    rw [sum_mul]
    apply sum_congr rfl
    intro t _
    ring
  have col : c.columns*A ≤ columnSlots k A c.m c.M c.v c.h+c.moment*k := by
    rw [←cf.2.2,←cf.2.1, columnSlots, mul_sum, sum_mul, sum_mul, ←sum_add_distrib]
    apply sum_le_sum
    intro t _
    have sub : c.m*A ≤ c.m*A-k*t+k*t := by omega
    have term := Nat.mul_le_mul_right (weight c t) sub
    unfold weight at *
    nlinarith only [term]
  change rowSlots n c.m c.M c.v c.h < columnSlots k A c.m c.M c.v c.h
  change c.rows*n+c.moment*k<c.columns*A at ha
  omega

private theorem cover {x : ℝ} (hl : 747/3000 ≤ x) (hu : x ≤ 2125/3000) :
    ∃ i, (prof i).left/3000 ≤ x ∧ x ≤ (prof i).right/3000 := by
  by_cases h₁ : x≤1125/3000
  · exact ⟨0,hl,h₁⟩
  by_cases h₂ : x≤1500/3000
  · exact ⟨1,(not_le.mp h₁).le,h₂⟩
  by_cases h₃ : x≤1875/3000
  · exact ⟨2,(not_le.mp h₂).le,h₃⟩
  exact ⟨3,(not_le.mp h₃).le,hu⟩

private theorem chord (i : Fin 4) (x : ℝ) (hl : (prof i).left/3000≤x)
    (hu : x≤(prof i).right/3000) :
    (prof i).rows+(prof i).moment*x^2 < (prof i).columns*(x-11/1000) := by
  have q := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)
  fin_cases i <;> norm_num [prof] at * <;> nlinarith only [hl,hu,q]

private theorem theta_gap {x : ℝ} (hl : 747/3000 ≤ x) (hu : x ≤ 2125/3000) :
    1+5*x^2 ≤ 6*(x-11/1000) := by
  nlinarith only [hl,hu,mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hu)]

private theorem select_profile {n k : ℕ} (hn : 4096≤n) (hlo : n≤16*k) (hhi : 2*k≤n) :
    ∃ (i : Fin 4) (A : ℕ), k<A ∧ A≤n ∧ k+1≤3*(A-k) ∧
      (n-k:ℕ) ≤ 6*(A-k) ∧
      1-Real.sqrt (((k:ℝ)-1)/n)+1/100 ≤ 1-(A:ℝ)/n ∧
      rowSlots n (prof i).m (prof i).M (prof i).v (prof i).h <
        columnSlots k A (prof i).m (prof i).M (prof i).v (prof i).h := by
  let x := Real.sqrt (((k:ℝ)-1)/n)
  have nr : (4096:ℝ)≤n := by exact_mod_cast hn
  have nn : (0:ℝ)<n := by linarith
  have kr : (n:ℝ)≤16*k := by exact_mod_cast hlo
  have kr' : (2:ℝ)*k≤n := by exact_mod_cast hhi
  have divpos : 0≤((k:ℝ)-1)/n := div_nonneg (by linarith) nn.le
  have xl : 747/3000≤x := (Real.le_sqrt (by norm_num) divpos).mpr
    ((le_div_iff₀ nn).mpr (by linarith))
  have xu : x≤2125/3000 := Real.sqrt_le_iff.mpr ⟨by norm_num,
    (div_le_iff₀ nn).mpr (by linarith)⟩
  have xs : x^2*(n:ℝ)=(k:ℝ)-1 := by
    dsimp only [x]
    rw [Real.sq_sqrt divpos, div_mul_cancel₀ _ nn.ne']
  let A : ℕ := ⌊(x-1/100)*(n:ℝ)⌋₊
  have Aupper : (A:ℝ)≤(x-1/100)*n := Nat.floor_le (mul_nonneg (by linarith) nn.le)
  have Alower : (x-11/1000)*(n:ℝ)+2 < A := by
    have h := Nat.lt_floor_add_one ((x-1/100)*(n:ℝ))
    change (x-1/100)*(n:ℝ)<(A:ℝ)+1 at h
    linarith
  have An : A≤n := by
    exact_mod_cast (show (A:ℝ)≤n by nlinarith [mul_le_mul_of_nonneg_right xu nn.le])
  have theta := mul_le_mul_of_nonneg_right (theta_gap xl xu) nn.le
  have th : (n:ℝ)-k≤6*((A:ℝ)-k) := by linarith
  have kA : k<A := by exact_mod_cast (show (k:ℝ)<A by linarith)
  have kn : k≤n := by omega
  obtain ⟨i,il,iu⟩ := cover xl xu
  let c := prof i
  have nums : c.moment≤2*c.columns ∧ 0<c.columns ∧ 0<c.v ∧ c.M≤12 := by
    fin_cases i <;> decide
  have slot : rowSlots n c.m c.M c.v c.h < columnSlots k A c.m c.M c.v c.h := by
    apply slots_of_affine i
    have mC : (c.moment:ℝ)≤2*c.columns := by exact_mod_cast nums.1
    have Cpos : (0:ℝ)<c.columns := by exact_mod_cast nums.2.1
    have q := mul_lt_mul_of_pos_right (chord i x il iu) nn
    change ((c.rows:ℝ)+c.moment*x^2)*n < c.columns*(x-11/1000)*n at q
    have low := mul_lt_mul_of_pos_left Alower Cpos
    have mK := congrArg (fun z : ℝ => c.moment*z) xs
    exact_mod_cast (show (c.rows:ℝ)*n+c.moment*k < c.columns*A by linarith only [mC,mK,low,q])
  have shape : 4*x^2 ≤ 3*(x-11/1000) := by
    nlinarith only [xl,xu,mul_nonneg (sub_nonneg.mpr xl) (sub_nonneg.mpr xu)]
  have shape' := mul_le_mul_of_nonneg_right shape nn.le
  refine ⟨i,A,kA,An,?_,?_,?_,slot⟩
  · zify [kA.le]
    have : (k:ℝ)+1≤3*((A:ℝ)-k) := by linarith
    exact_mod_cast this
  · exact_mod_cast (show ((n-k:ℕ):ℝ) ≤ 6*((A-k:ℕ):ℝ) by
      rwa [Nat.cast_sub kn,Nat.cast_sub kA.le])
  · have As := (div_le_iff₀ nn).mpr Aupper
    change 1-x+1/100 ≤ 1-(A:ℝ)/n
    linarith

/-- Every rate in `[1/16,1/2]` admits a full percentage point past the
finite-length Johnson radius on every prime-field domain of length at least
4096. The field requirement is uniform across the interval. -/
theorem uniform_one_percent_error {n k : ℕ} {F : Type} [Field F] [Fintype F] [SampleableType F]
    (hn : 4096≤n) (hlo : n≤16*k) (hhi : 2*k≤n)
    (hchar : ringChar F=0 ∨ max (k-1) 12 < ringChar F) (dom : Fin n ↪ F) :
    mcaError (AffineLineGenerator F) (code dom k)
      (1-Real.sqrt (((k:ℝ)-1)/n)+1/100) ≤ ENNReal.ofReal ((2:ℝ)^31*n^2/Fintype.card F) := by
  classical
  obtain ⟨i,A,kA,An,_,htheta,hr,slot⟩ := select_profile hn hlo hhi
  let c := prof i
  have nums : 0<c.v ∧ c.M≤12 := by fin_cases i <;> decide
  have th : ((n:ℝ)-k)≤6*((A:ℝ)-k) := by
    have := (show ((n-k:ℕ):ℝ)≤6*((A-k:ℕ):ℝ) by exact_mod_cast htheta)
    rwa [Nat.cast_sub (by omega : k≤n), Nat.cast_sub kA.le] at this
  have envelope : ((2*c.v-1 : ℕ) : ℝ)*c.h + 6*(c.h+c.v) +
      (4*6*(1/2:ℝ)*c.v*c.h+c.v+8*(1/2:ℝ)*6^2*stageStaircase c.v c.M) +
      (24*(1/2:ℝ)^2*c.h*6^2*stageStaircase c.v c.M+4*(1/2:ℝ)*6*stageStaircase c.v c.M) ≤
      (2^31:ℕ) := by
    fin_cases i <;> norm_num [c,prof,stageStaircase]
  have hD : 0<k-1 := by omega
  have hsucc : k=k-1+1 := by omega
  have hDA : k-1<A := by omega
  have Dc : ((k-1:ℕ):ℝ) ≤ (1/2:ℝ)*n := by
    rw [Nat.cast_sub (by omega)]
    have hk : (2:ℝ)*k≤n := by exact_mod_cast hhi
    push_cast
    linarith
  have ratio : agreementIncidenceRatio n (k-1) A ≤ 6 := by
    unfold agreementIncidenceRatio
    apply (div_le_iff₀ (by exact_mod_cast Nat.sub_pos_of_lt hDA)).mpr
    simp only [Nat.cast_sub (by omega : k-1≤n), Nat.cast_sub (by omega : k-1≤A),Nat.cast_sub (by omega : 1≤k)]
    push_cast
    linarith
  have line : LineExactAgreementBound dom k A ((2:ℝ)^31*n^2) := by
    apply lineExactAgreementBound_of_exactCorrelatedPair
    intro f g
    have hs := scaled_slots (b:=1) (by decide) slot
    simp only [one_mul] at hs
    obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (k:=k) hD hsucc.le dom f g hs
    have ch : ringChar F=0 ∨ max (k-1) c.M < ringChar F := by
      rcases hchar with hz|hh
      · exact Or.inl hz
      · right; omega
    obtain ⟨E,_,_,hc,hfit⟩ := cert.exists_exceptional_hybrid hsucc hD hDA ch
    refine ⟨E,hc.trans ((exception_le (by omega : 1≤n) (by norm_num : (0:ℝ)≤1/2) Dc ratio
      nums.1 (le_rfl : stageStaircase c.v c.M ≤ _)).trans ?_), hfit⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast envelope) (sq_nonneg (n:ℝ))
  apply mcaError_affineLine_le_of_exactAgreement dom _ line
  rw [Fintype.card_fin]
  have nn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha := (div_le_iff₀ nn).mp (show (A:ℝ)/n ≤ 1-(1-Real.sqrt (((k:ℝ)-1)/n)+1/100) by linarith)
  calc A = ⌈(A:ℝ)⌉₊ := (Nat.ceil_natCast A).symm
       _ ≤ _ := Nat.ceil_mono (by linarith)

/-- In particular a field of order at least `2^159 n²` gives the 128-bit
line-MCA guarantee on every prescribed prime-field domain in this rate band. -/
theorem uniform_one_percent {n k p : ℕ} [Fact p.Prime] [SampleableType (ZMod p)]
    (hn : 4096≤n) (hlo : n≤16*k) (hhi : 2*k≤n) (hp : 2^159*n^2≤p)
    (dom : Fin n ↪ ZMod p) :
    mcaError (AffineLineGenerator (ZMod p)) (code dom k)
      (1-Real.sqrt (((k:ℝ)-1)/n)+1/100) ≤ ENNReal.ofReal (1/(2:ℝ)^128) := by
  have hnfield := Fintype.card_le_of_injective _ dom.injective
  rw [Fintype.card_fin,ZMod.card] at hnfield
  have ch : ringChar (ZMod p)=0 ∨ max (k-1) 12<ringChar (ZMod p) := by
    right; rw [ZMod.ringChar_zmod_n]; omega
  apply (uniform_one_percent_error hn hlo hhi ch dom).trans
  rw [ZMod.card]
  apply ENNReal.ofReal_le_ofReal
  apply (div_le_div_iff₀ (by exact_mod_cast (Fact.out : p.Prime).pos) (by norm_num : (0:ℝ)<2^128)).mpr
  have h : (2:ℝ)^159*(n:ℝ)^2 ≤ p := by exact_mod_cast hp
  norm_num at h ⊢
  linarith

private theorem weight_identity (k v M : ℕ) :
    firstOrderListWeight k v M + k*firstOrderListWeight 0 v M =
      firstOrderListWeight 0 v M+k*firstOrderListWeight 1 v M := by
  induction v generalizing M with
  | zero => simp [firstOrderListWeight]
  | succ v ih =>
    cases M with
    | zero => simp only [firstOrderListWeight]; nlinarith only [ih 0]
    | succ M => simp only [firstOrderListWeight]; nlinarith only [ih M]

/-- The same radius has a linear worst-case list on every supplied domain
in characteristic zero or characteristic at least the length. -/
theorem uniform_one_percent_list {n k : ℕ} {F : Type*} [Field F]
    (hn : 4096≤n) (hlo : n≤16*k) (hhi : 2*k≤n)
    (hfield : ringChar F=0 ∨ n≤ringChar F) (dom : Fin n ↪ F) :
    Code.Lambda (code dom k : Set (Fin n → F)) (1-Real.sqrt (((k:ℝ)-1)/n)+1/100) ≤
      ((174000*n:ℕ):ℕ∞) := by
  obtain ⟨i,A,kA,An,gap,_,hr,slot⟩ := select_profile hn hlo hhi
  let c := prof i
  have weight : firstOrderListWeight k c.v c.M ≤ 58000*(k+1) := by
    have nums : firstOrderListWeight 0 c.v c.M≤1540 ∧
        firstOrderListWeight 1 c.v c.M≤firstOrderListWeight 0 c.v c.M+57904 := by
      fin_cases i <;> decide
    nlinarith only [nums.1, Nat.mul_le_mul_left k nums.2, weight_identity k c.v c.M]
  have cost : firstOrderListWeight k c.v c.M ≤ 174000*(A-k) := by omega
  have vh : c.v≤55 := by fin_cases i <;> decide
  have h := list_of_slots (b:=1) (N:=n) (k:=k) (A:=A) (m:=c.m) (M:=c.M) (μ:=c.v)
    (h:=c.h) (C:=174000) (by decide) (by omega) kA An (by omega) (by simpa only [one_mul] using hfield)
    cost slot
  apply (Code.Lambda_mono hr).trans
  have transport (N : ℕ) (eN : 1*n=N) (d : Fin N ↪ F) :
      Code.Lambda (code d k : Set (Fin N → F)) (1-(A:ℝ)/n) ≤ ((174000*n:ℕ):ℕ∞) := by
    subst N
    simpa only [Nat.one_mul] using h d
  exact transport n (Nat.one_mul n) dom

/-- The full linear list bound holds at every interleaving width in every
prime field admitting the prescribed domain. -/
theorem uniform_one_percent_interleaved_list {n k p : ℕ} [Fact p.Prime]
    (hn : 4096≤n) (hlo : n≤16*k) (hhi : 2*k≤n) (dom : Fin n ↪ ZMod p) (width : ℕ) :
    Code.Lambda (Code.interleavedCodeSet (κ:=Fin width) (code dom k : Set (Fin n → ZMod p)))
      (1-Real.sqrt (((k:ℝ)-1)/n)+1/100) ≤ ((174000*n:ℕ):ℕ∞) := by
  let φ := algebraMap (ZMod p) (RatFunc (ZMod p))
  have hp : n≤p := by simpa using Fintype.card_le_of_injective dom dom.injective
  have ch : ringChar (RatFunc (ZMod p)) = p := ringChar.eq _ p
  exact (Lambda_interleaved_le_ratFunc dom k width _).trans
    (uniform_one_percent_list hn hlo hhi (Or.inr (hp.trans_eq ch.symm)) (dom.trans ⟨φ,φ.injective⟩))

end ProximityGap.RateIntervalJohnsonGain

#print axioms ProximityGap.RateIntervalJohnsonGain.uniform_one_percent_error
#print axioms ProximityGap.RateIntervalJohnsonGain.uniform_one_percent
#print axioms ProximityGap.RateIntervalJohnsonGain.uniform_one_percent_interleaved_list
