/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.ClosedManyLinePhase

/-! # From a finite many-line construction to its exact phase

A finite construction supplies all r(e+1) labels whenever field size, locator
degree and the number of pairs of sites meet its separation test. The cost
coefficient is independent of length. The limiting packing, moment and
core-geometry calculations then apply to each such construction.
-/
set_option autoImplicit false
namespace ProximityGap.ManyLineGridPhase
open Filter Topology MCAThresholdLedger GeneralTwoLineArithmetic
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal
variable (F : ℕ → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)] [∀ i, DecidableEq (F i)]
    (n k : ℕ → ℕ) [∀ i, NeZero (n i)] (x : ∀ i, Fin (n i) ↪ F i)

/-- Finite bad-scalar lower bound for a construction with separation cost
c per ordered pair of sites and r distinct affine heads. -/
def GridAttack (r c : ℕ) : Prop :=
  ∀ (i e : ℕ), 2≤k i → k i+e+1≤n i → r*(n i-k i+1-e)≤n i-k i+2 →
    n i^2*c≤(Fintype.card (F i)-1)*(k i-2) →
    ((r*(e+1):ℕ):ℝ≥0∞)/(Fintype.card (F i)) ≤
      epsMCA (F:=F i) (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) ((e:ℝ≥0)/n i)

omit [∀ i, DecidableEq (F i)] in
/-- Sufficiently long prescribed domains admit r(e+1) distinct bad labels
under the strict packing and linear field-size hypotheses. -/
theorem eventually_attack (e : ℕ → ℕ) (r c : ℕ) (grid : GridAttack F n k x r c) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (fieldSize : (c:ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, ((r*(e i+1):ℕ):ℝ≥0∞)/(Fintype.card (F i)) ≤
      epsMCA (F:=F i) (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → F i)) ((e i:ℝ≥0)/n i) := by
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have two := tiny.eventually_lt rate positive
  have sum := ((rate.add err).add tiny).eventually_lt_const (by simpa using core)
  have complement := (tendsto_const_nhds (x:=(1:ℝ))).sub rate
  have pk := (((complement.add tiny).sub err).const_mul (r:ℝ)).eventually_lt
    (complement.add (tiny.const_mul 2)) (by simpa using packing)
  have field := ((hf.sub tiny).mul (rate.sub (tiny.const_mul 2))).eventually_const_lt
    (by simpa using fieldSize)
  filter_upwards [two,sum,pk,field] with i ki cap pack size
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1/(n i:ℝ)<(k i:ℝ)/n i at ki
  have hk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp ki
  change (k i:ℝ)/n i+(e i:ℝ)/n i+1/n i < 1 at cap
  rw [←add_div,←add_div,div_lt_one ni] at cap
  have inside : k i+e i+1 ≤ n i := by exact_mod_cast cap.le
  have ku : k i≤n i := by omega
  have ee : e i≤n i-k i+1 := by omega
  change (r:ℝ)*(1-(k i:ℝ)/n i+1/n i-(e i:ℝ)/n i) < (1-(k i:ℝ)/n i)+2*(1/n i) at pack
  change (c:ℝ) < ((Fintype.card (F i):ℝ)/n i-1/n i)*((k i:ℝ)/n i-2*(1/n i)) at size
  field_simp [ni.ne'] at pack size
  have packNat : r*(n i-k i+1-e i)≤n i-k i+2 := by
    have h : (r:ℝ)*((n i:ℝ)-k i+1-e i)≤(n i:ℝ)-k i+2 := by nlinarith only [pack]
    simp only [←Nat.cast_sub ku,←Nat.cast_add_one,←Nat.cast_sub ee] at h
    exact_mod_cast h
  have room : n i^2*c≤(Fintype.card (F i)-1)*(k i-2) := by
    have h : ((n i^2*c:ℕ):ℝ)≤(((Fintype.card (F i)-1)*(k i-2):ℕ):ℝ) := by
      push_cast [Nat.cast_sub (Fintype.card_pos (α:=F i)),Nat.cast_sub hk]
      nlinarith only [size]
    exact_mod_cast h
  exact grid i (e i) hk inside packNat room

/-- An arbitrary injective domain has exactly r(e+1) worst-pair bad labels
in the strict many-line incidence range. -/
theorem eventually_mass (e : ℕ → ℕ) (r c : ℕ) (grid : GridAttack F n k x r c) (hr : 1≤r) (hn : Tendsto n atTop atTop)
    {slope ρ b : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 b)) (hb : 0<b) (core : ρ+b<1)
    (packing : (r:ℝ)*(1-ρ-b)<1-ρ) (moment : ρ<(1-b)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-b))
    (fieldSize : (c:ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, epsMCA (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) ((e i:ℝ≥0)/n i) = ((r*(e i+1):ℕ):ℝ≥0∞)/(Fintype.card (F i)) := by
  have attack := eventually_attack F n k x e r c grid hn hf rate positive err core packing fieldSize
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have two := tiny.eventually_lt rate positive
  have sum := (rate.add err).eventually_lt_const core
  obtain ⟨L,hL,conditions⟩ := eventually_many_line_hypotheses r n k e hn hb (by linarith) err rate moment geometry
  filter_upwards [attack,two,sum,conditions] with i lo ki cap num
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1/(n i:ℝ)<(k i:ℝ)/n i at ki
  have hk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp ki
  change (k i:ℝ)/n i+(e i:ℝ)/n i < 1 at cap
  rw [←add_div,div_lt_one ni] at cap
  have inside : k i+e i ≤ n i := by exact_mod_cast cap.le
  apply le_antisymm _ lo
  apply GeneralManyLineSafety.epsMCA_le (x i) _ (Fintype.card_fin _) (by omega)
    (by omega) (by omega) hL hr _ num.2.1 num.2.2
  rw [Fintype.card_fin,tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),
    ←Nat.cast_tsub,Nat.ceil_natCast]

/-- In the open range the first failed grid index is eventually the integer
budget divided by r and rounded down, on every prescribed domain. -/
theorem exact_threshold (r c Q : ℕ) (grid : GridAttack F n k x r c) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : a=slope/Q/r) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)<1-ρ) (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : (c:ℝ)<slope*ρ) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)) = ((Fintype.card (F i)/Q/r:ℕ):ℝ≥0)/n i := by
  let j i := Fintype.card (F i)/Q/r
  have jl : Tendsto (fun i => (j i:ℝ)/n i) atTop (𝓝 a) := by
    rw [index]
    exact LinearFieldBudgetLimit.floor_limit _ n r hr hn (LinearFieldBudgetLimit.floor_limit _ n Q hQ hn hf)
  have lo := eventually_mass F n k x (fun i => j i-1) r c grid hr hn hf rate positive
    (previous_limit j n hn ha jl) ha core packing moment geometry fieldSize
  have hi := eventually_mass F n k x j r c grid hr hn hf rate positive jl ha core packing moment geometry fieldSize
  have small := jl.eventually_lt_const (show a<1 by linarith)
  filter_upwards [lo,hi,small,jl.eventually_const_lt ha] with i prev cur jn jp
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  have jpNat : 0<j i := by exact_mod_cast (div_pos_iff_of_pos_right ni).mp jp
  have jnNat : j i≤n i := by exact_mod_cast ((div_lt_one ni).mp jn).le
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    rw [cur]
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ]
    exact Nat.not_le_of_lt <| Nat.lt_mul_div_succ _ hr
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good jpNat jnNat
    unfold predecessorRadius
    rw [prev,BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ]
    rw [Nat.sub_add_cancel jpNat]
    simpa [j,Nat.mul_comm] using Nat.div_mul_le_self (Fintype.card (F i)/Q) r

/-- The limiting radius is the rth share of the scalar budget even on the
three boundary faces of the phase. Only the field-size separation test
retains a strict margin. -/
theorem limit (r c Q : ℕ) (grid : GridAttack F n k x r c) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop)
    {slope ρ a : ℝ} (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : (r:ℝ)*a=slope/Q) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)≤1-ρ) (moment : ρ≤(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ ≤ ((r+1:ℕ):ℝ)*(1-a))
    (fieldSize : (c:ℝ)<slope*ρ) :
    Tendsto (fun i => (mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
      Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)):ℝ)) atTop (𝓝 a) := by
  apply tendsto_order.mpr
  constructor
  · intro s hs
    exact ClosedManyLinePhase.eventually_above F n k x Q r hr hQ hn hf rate positive index ha core moment geometry hs
  · intro s hs
    obtain ⟨b,lb,ub⟩ := exists_between (lt_min hs (show a<1-ρ by linarith))
    have rp : (0:ℝ)<r := by exact_mod_cast hr
    have err := SmoothLinearFieldEnvelope.floor_fraction n hn (ha.trans lb).le
    have less := mul_lt_mul_of_pos_left (show 1-ρ-b<1-ρ-a by linarith) rp
    have attack := eventually_attack F n k x _ r c grid hn hf rate positive err
      (by have := ub.trans_le (min_le_right _ _);linarith) (less.trans_le packing) fieldSize
    have overBudget := (LinearFieldBudgetLimit.floor_limit (fun i => Fintype.card (F i)) n Q hQ hn hf).eventually_lt
      (err.const_mul (r:ℝ)) (index ▸ mul_lt_mul_of_pos_left lb rp)
    have below := err.eventually_lt_const (ub.trans_le (min_le_left _ _))
    filter_upwards [attack,overBudget,below] with i lo excess lt
    let e := ⌊b*(n i:ℝ)⌋₊
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    change ((Fintype.card (F i)/Q:ℕ):ℝ)/n i < (r:ℝ)*((e:ℝ)/n i) at excess
    rw [←mul_div_assoc,div_lt_div_iff_of_pos_right ni] at excess
    have ex : Fintype.card (F i)/Q < r*e := by exact_mod_cast excess
    have upper : mcaDeltaStar (F:=F i) (ReedSolomon.code (x i) (k i) :
        Set (Fin (n i) → F i)) (1/(Q:ℝ≥0∞)) ≤ (e:ℝ≥0)/n i := by
      apply mcaDeltaStar_le_of_bad
      apply lt_of_lt_of_le _ lo
      apply lt_of_not_ge
      rw [BoundarySecurityBudget.count_ratio_le_iff Fintype.card_pos hQ]
      exact Nat.not_le_of_lt (ex.trans_le (Nat.mul_le_mul_left r (Nat.le_succ e)))
    exact lt_of_le_of_lt (by exact_mod_cast upper) lt

end ProximityGap.ManyLineGridPhase
#print axioms ProximityGap.ManyLineGridPhase.eventually_attack
#print axioms ProximityGap.ManyLineGridPhase.eventually_mass
#print axioms ProximityGap.ManyLineGridPhase.exact_threshold
#print axioms ProximityGap.ManyLineGridPhase.limit
