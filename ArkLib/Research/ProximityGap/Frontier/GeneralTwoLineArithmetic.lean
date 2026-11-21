/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.CriticalLinearBudget

/-! # Many-line safety inequalities at a fixed limiting agreement fraction
The cubic inequality compares a triple agreement count to degree. The linear
inequality ensures an outsider cannot meet the cores of the selected rich lines often
enough. Both inequalities hold eventually under strict limiting inequalities.
-/
set_option autoImplicit false
namespace ProximityGap.GeneralTwoLineArithmetic
open Filter Topology

/-- Taking a predecessor error index has the same normalized limit. -/
theorem previous_limit (j n : ℕ → ℕ) [∀ i, NeZero (n i)] (hn : Tendsto n atTop atTop)
    {a : ℝ} (ha : 0<a) (limit : Tendsto (fun i => (j i:ℝ)/n i) atTop (𝓝 a)) :
    Tendsto (fun i => ((j i-1:ℕ):ℝ)/n i) atTop (𝓝 a) := by
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have pos := limit.eventually_const_lt ha
  have h := limit.sub tiny
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [pos] with i hi
  have ji : 1≤j i := by by_contra! contra; simp [show j i=0 by omega] at hi
  simp [Nat.cast_sub ji,sub_div]

/-- One fixed line occupancy cut works eventually for all lengths in the
sequence. Here e denotes errors and n-e is the agreement threshold. -/
theorem eventually_many_line_hypotheses (r : ℕ) (n k e : ℕ → ℕ) [∀ i, NeZero (n i)]
    (hn : Tendsto n atTop atTop) {a ρ : ℝ} (ha : 0<a) (ha₁ : a<1)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 a))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (moment : ρ<(1-a)^3) (geom : 1+((r.choose 2+r:ℕ):ℝ)*ρ<((r+1:ℕ):ℝ)*(1-a)) :
    ∃ L : ℕ, 2≤L ∧ ∀ᶠ i in atTop,
      e i≤n i ∧ (e i+2)*k i*n i^2+(L+2)*n i^3 < (e i+2)*(n i-e i)^3 ∧
      (n i+(r.choose 2+r)*k i)*L+r*n i < (r+1)*(n i-e i)*L := by
  let c := r.choose 2+r
  let s := r+1
  let gap := (s:ℝ)*(1-a)-(1+(c:ℝ)*ρ)
  have gp : 0<gap := sub_pos.mpr geom
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 ((r:ℝ)/gap))
  have L2 : 2≤L := by exact_mod_cast (lt_of_le_of_lt (le_max_left ..) hL : (1:ℝ)<L)
  have margin := (div_lt_iff₀ gp).mp ((le_max_right ..).trans_lt hL)
  have limGeom : (1+(c:ℝ)*ρ)*(L:ℝ)+(r:ℝ)<(s:ℝ)*(1-a)*(L:ℝ) := by dsimp [gap] at margin; nlinarith
  let t i := n i-e i
  have below := err.eventually_lt_const ha₁
  have en : ∀ᶠ i in atTop, e i≤n i := by
    filter_upwards [below] with i hi
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    exact_mod_cast (div_lt_one ni).mp hi |>.le
  have one : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have tiny := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have limT : Tendsto (fun i => (t i:ℝ)/n i) atTop (𝓝 (1-a)) := by
    apply (one.sub err).congr'
    filter_upwards [en] with i le
    simp [t,Nat.cast_sub le,sub_div]
  have limM : Tendsto (fun i => ((e i:ℝ)+2)/n i) atTop (𝓝 a) := by
    simpa [div_eq_mul_inv,add_mul] using err.add (tiny.const_mul 2)
  have ml := (limM.mul rate).add (tiny.const_mul ((L:ℝ)+2))
  have mr := limM.mul (limT.pow 3)
  have cmp := ml.eventually_lt mr (by simpa using (mul_lt_mul_of_pos_left moment ha))
  have gl := (((one.add (rate.const_mul (c:ℝ))).mul_const (L:ℝ)).add (tendsto_const_nhds (x:=(r:ℝ))))
  have gr := (limT.const_mul (s:ℝ)).mul_const (L:ℝ)
  have gcmp := gl.eventually_lt gr limGeom
  refine ⟨L,L2,?_⟩
  filter_upwards [en,cmp,gcmp] with i le h g
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change ((e i:ℝ)+2)/n i*((k i:ℝ)/n i)+((L:ℝ)+2)*(1/n i) <
    ((e i:ℝ)+2)/n i*((t i:ℝ)/n i)^3 at h
  change (1+(c:ℝ)*((k i:ℝ)/n i))*(L:ℝ)+(r:ℝ) < (s:ℝ)*((t i:ℝ)/n i)*(L:ℝ) at g
  field_simp at h g
  refine ⟨le,?_,?_⟩
  · exact_mod_cast (show ((e i:ℝ)+2)*k i*(n i:ℝ)^2+((L:ℝ)+2)*(n i:ℝ)^3 < ((e i:ℝ)+2)*(t i:ℝ)^3
      by nlinarith only [h])
  · exact_mod_cast (show ((n i:ℝ)+(c:ℝ)*k i)*L+(r:ℝ)*(n i:ℝ) < (s:ℝ)*(t i:ℝ)*L by nlinarith only [g])

/-- One fixed line occupancy cut works eventually for all lengths in the
sequence. Here e denotes errors and n-e is the agreement threshold. -/
theorem eventually_hypotheses (n k e : ℕ → ℕ) [∀ i, NeZero (n i)]
    (hn : Tendsto n atTop atTop) {a ρ : ℝ} (ha : 0<a) (ha₁ : a<1)
    (err : Tendsto (fun i => (e i:ℝ)/n i) atTop (𝓝 a))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (moment : ρ<(1-a)^3) (geom : 1+3*ρ<3*(1-a)) :
    ∃ L : ℕ, 2≤L ∧ ∀ᶠ i in atTop,
      e i≤n i ∧ (e i+2)*k i*n i^2+(L+2)*n i^3 < (e i+2)*(n i-e i)^3 ∧
      (n i+3*k i)*L+2*n i < 3*(n i-e i)*L := by
  simpa using eventually_many_line_hypotheses 2 n k e hn ha ha₁ err rate moment
    (by simpa using geom)

end ProximityGap.GeneralTwoLineArithmetic
#print axioms ProximityGap.GeneralTwoLineArithmetic.eventually_hypotheses
#print axioms ProximityGap.GeneralTwoLineArithmetic.eventually_many_line_hypotheses
