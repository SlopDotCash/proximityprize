/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.GeneralManyLineSafety
import ArkLib.Research.ProximityGap.Frontier.GeneralTwoLineArithmetic

/-! # Exact many-line phases on smooth prime-field domains

A strict limiting packing test supplies an attack on r heads. Third moments
and pairwise core intersections give the matching upper bound for every
received pair, certifying the first failing error index at the rth part
of the integer challenge budget.
-/

set_option autoImplicit false
namespace ProximityGap.SmoothManyLinePhase
open Filter Topology MCAThresholdLedger GeneralTwoLineArithmetic CosetHeadSlopes
open ArkLib.ProximityGap.Frontier.PrizeShapeRateHalfBracket
open scoped NNReal ENNReal

/-- At fixed rate and field-size slope, each sufficiently long prescribed
smooth code has exactly r(e+1) worst-case bad challenges in the strict
many-line range. -/
theorem eventually_mass (p n k e : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (r : ℕ) (hr : 1≤r) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 a)) (ha : 0<a)
    (core : ρ+a<1) (packing : (r:ℝ)*(1-ρ-a) < 1-ρ)
    (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (supply : (((edges (r+1)).offDiag.card*r : ℕ):ℝ)<slope) :
    ∀ᶠ i in atTop, epsMCA (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) ((e i:ℝ≥0)/n i) =
      ((r*(e i+1):ℕ):ℝ≥0∞)/(p i) := by
  let N := (edges (r+1)).card
  let P := (edges (r+1)).offDiag.card
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have two := tiny.eventually_lt rate positive
  have sum := ((rate.add err).add tiny).eventually_lt_const (by simpa using core)
  have c := (tendsto_const_nhds (x:=(1:ℝ))).sub rate
  have pk := (((c.add tiny).sub err).const_mul (r:ℝ)).eventually_lt
    (c.add (tiny.const_mul 2)) (by simpa using packing)
  have room := (((tiny.const_mul (N:ℝ)).add (tendsto_const_nhds (x:=(P:ℝ)))).mul_const (r:ℝ)).eventually_lt hf
    (by simpa [P] using supply)
  obtain ⟨L,hL,conditions⟩ := eventually_many_line_hypotheses r n k e hn ha (by linarith) err rate moment geometry
  filter_upwards [two,sum,pk,room,conditions,eventually_ge_atTop (r+1) |> hn.eventually] with i ki cap pack size num long
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1/(n i:ℝ)<(k i:ℝ)/n i at ki
  have hk : 2≤k i := by exact_mod_cast (div_lt_div_iff_of_pos_right ni).mp ki
  change (k i:ℝ)/n i+(e i:ℝ)/n i+1/n i < 1 at cap
  rw [←add_div,←add_div,div_lt_one ni] at cap
  have inside : k i+e i+1 ≤ n i := by exact_mod_cast cap.le
  have ku : k i≤n i := by omega
  have ee : e i≤n i-k i+1 := by omega
  change (r:ℝ)*(1-(k i:ℝ)/n i+1/n i-(e i:ℝ)/n i) < (1-(k i:ℝ)/n i)+2*(1/n i) at pack
  change ((N:ℝ)*(1/n i)+(P:ℝ))*(r:ℝ)<(p i:ℝ)/n i at size
  field_simp at pack size
  have packNat : r*(n i-k i+1-e i)≤n i-k i+2 := by
    have h : (r:ℝ)*((n i:ℝ)-k i+1-e i)≤(n i:ℝ)-k i+2 := by nlinarith only [pack]
    simp only [←Nat.cast_sub ku,←Nat.cast_add_one,←Nat.cast_sub ee] at h
    exact_mod_cast h
  have supplyNat : (N+P*n i)*r<p i := by
    exact_mod_cast (show ((N:ℝ)+(P:ℝ)*n i)*r < p i by nlinarith only [size])
  have xn : n i≤Fintype.card (ZMod (p i)) := by simpa using Fintype.card_le_of_injective _ (x i).injective
  let b := (Fin.castLEEmb (long.trans xn)).trans (Fintype.equivFin (ZMod (p i))).symm.toEmbedding
  have equal := GeneralManyLineSafety.epsMCA_eq (k:=k i) (t:=n i-e i) (e:=e i)
    (x i) ((e i:ℝ≥0)/n i) b (by omega) hk (by omega) hL hr
    (by rw [tsub_mul,one_mul,div_mul_cancel₀ _ (by exact_mod_cast NeZero.ne (n i)),←Nat.cast_tsub,Nat.ceil_natCast])
    num.2.1 num.2.2 (by rw [show n i-e i-1-(k i-2)=n i-k i+1-e i by omega];omega)
    (by simpa only [ZMod.card] using supplyNat)
  simpa only [ZMod.card] using equal

/-- In the open many-line phase the operational radius is eventually the
literal rth part of the integer scalar budget, rounded down, divided by n. -/
theorem exact_threshold (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : a=slope/Q/r) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)<1-ρ) (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (supply : (((edges (r+1)).offDiag.card*r : ℕ):ℝ)<slope) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) =
      ((p i/Q/r:ℕ):ℝ≥0)/n i := by
  let j i := p i/Q/r
  have jl : Tendsto (fun i => (j i:ℝ)/n i) atTop (𝓝 a) := by
    rw [index]
    exact LinearFieldBudgetLimit.floor_limit _ n r hr hn (LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf)
  have lo := eventually_mass p n k (fun i => j i-1) x r hr hn hf rate positive
    (previous_limit j n hn ha jl) ha core packing moment geometry supply
  have hi := eventually_mass p n k j x r hr hn hf rate positive jl ha core packing moment geometry supply
  have small := jl.eventually_lt_const (show a<1 by linarith)
  filter_upwards [lo,hi,small,jl.eventually_const_lt ha] with i prev cur jn jp
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  have jpNat : 0<j i := by exact_mod_cast (div_pos_iff_of_pos_right ni).mp jp
  have jnNat : j i≤n i := by exact_mod_cast ((div_lt_one ni).mp jn).le
  apply le_antisymm
  · apply mcaDeltaStar_le_of_bad
    rw [cur]
    apply lt_of_not_ge
    rw [BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=(p i).Prime)).pos hQ]
    exact Nat.not_le_of_lt <| Nat.lt_mul_div_succ _ hr
  · apply latticeBoundary_le_mcaDeltaStar_of_predecessor_good jpNat jnNat
    unfold predecessorRadius
    rw [prev,BoundarySecurityBudget.count_ratio_le_iff (Fact.out (p:=(p i).Prime)).pos hQ]
    rw [Nat.sub_add_cancel jpNat]
    simpa [j,Nat.mul_comm] using Nat.div_mul_le_self (p i/Q) r

/-- The limiting MCA radius equals the field-size slope divided by the
security denominator and the number of heads. -/
theorem threshold_limit (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (r Q : ℕ) (hr : 1≤r) (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ a : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (index : a=slope/Q/r) (ha : 0<a) (core : ρ+a<1)
    (packing : (r:ℝ)*(1-ρ-a)<1-ρ) (moment : ρ<(1-a)^3)
    (geometry : 1+((r.choose 2+r:ℕ):ℝ)*ρ < ((r+1:ℕ):ℝ)*(1-a))
    (supply : (((edges (r+1)).offDiag.card*r : ℕ):ℝ)<slope) :
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)):ℝ))
      atTop (𝓝 a) := by
  have eq := exact_threshold p n k x r Q hr hQ hn hf rate positive index ha core packing moment geometry supply
  have target : Tendsto (fun i => ((p i/Q/r:ℕ):ℝ)/n i) atTop (𝓝 a) := by
    rw [index]
    exact LinearFieldBudgetLimit.floor_limit _ n r hr hn (LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf)
  apply target.congr'
  filter_upwards [eq] with i hi
  rw [hi]
  simp

end ProximityGap.SmoothManyLinePhase
#print axioms ProximityGap.SmoothManyLinePhase.eventually_mass
#print axioms ProximityGap.SmoothManyLinePhase.exact_threshold
#print axioms ProximityGap.SmoothManyLinePhase.threshold_limit
