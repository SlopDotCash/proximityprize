/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.SmoothManyHeadMass
import ArkLib.Research.ProximityGap.Frontier.SmoothDomainMcaEquivalence

/-! # Smooth many-head ceilings at fixed relative field size
For m active heads, there is a family of finite attacks above both the packing
threshold (1−1/m)(1−ρ) and the budget threshold λ/(mQ), including beyond the
half-distance plateau. All finite code sets remain prescribed inputs.
-/
set_option autoImplicit false
namespace ProximityGap.SmoothLinearFieldEnvelope
open Filter Topology CosetHeadSlopes MCAThresholdLedger
open scoped NNReal ENNReal

/-- Any error-count sequence tending to a relative error strictly inside the
many-head attack range eventually bounds the operational radius from above. -/
theorem eventually_ceiling (p n k e : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (d Q : ℕ) (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ α : ℝ}
    (hf : Tendsto (fun i => (p i : ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i : ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ)
    (err : Tendsto (fun i => (e i : ℝ)/n i) atTop (𝓝 α))
    (core : ρ+α<1) (pack : ((d+1:ℕ):ℝ)*(1-ρ-α) < 1-ρ)
    (fieldSize : (((edges (d+2)).offDiag.card*(d+1) : ℕ):ℝ) < slope)
    (overBudget : slope/Q < ((d+1:ℕ):ℝ)*α) :
    ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) ≤
      (e i : ℝ≥0)/n i := by
  let m := d+1
  let N := (edges (d+2)).card
  let P := (edges (d+2)).offDiag.card
  have small := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have htwo := small.eventually_lt rate positive
  have sum := ((rate.add err).add small).eventually_lt_const (by simpa using core)
  have c := (tendsto_const_nhds (x:=(1:ℝ))).sub rate
  have lhs := (((c.add small).sub err).const_mul (m:ℝ))
  have rhs := c.add (small.const_mul 2)
  have hpack := lhs.eventually_lt rhs (by simpa [m] using pack)
  have room := ((small.const_mul (N:ℝ)).add (tendsto_const_nhds (x:=(P:ℝ)))).mul_const (m:ℝ)
  have hroom := room.eventually_lt hf (by simpa [P,m] using fieldSize)
  have floor := LinearFieldBudgetLimit.floor_limit p n Q hQ hn hf
  have budget := floor.eventually_lt ((err.add small).const_mul (m:ℝ)) (by simpa [m] using overBudget)
  filter_upwards [htwo,sum,hpack,hroom,budget] with i k2 g pack_i size_i budget_i
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  change 1/(n i:ℝ)< (k i:ℝ)/n i at k2
  have hk : 2≤k i := by
    rw [div_lt_div_iff_of_pos_right ni] at k2
    exact_mod_cast k2
  change (k i:ℝ)/n i+(e i:ℝ)/n i+1/n i < 1 at g
  rw [←add_div,←add_div,div_lt_one ni] at g
  have inside : k i+e i+1 ≤ n i := by exact_mod_cast g.le
  have kn : k i≤n i := by omega
  have enough : e i≤n i-k i+1 := by omega
  change (m:ℝ)*(1-(k i:ℝ)/n i+1/n i-(e i:ℝ)/n i) <
    (1-(k i:ℝ)/n i)+2*(1/n i) at pack_i
  change ((N:ℝ)*(1/n i)+(P:ℝ))*(m:ℝ)<(p i:ℝ)/n i at size_i
  change ((p i/Q:ℕ):ℝ)/n i < (m:ℝ)*((e i:ℝ)/n i+1/n i) at budget_i
  field_simp at pack_i size_i budget_i
  apply SmoothManyHeadMass.ceiling_at_errors (d:=d) (x i) hk inside hQ
  · change m*(n i-k i+1-e i)≤n i-k i+2
    have q : (m:ℝ)*((n i:ℝ)-k i+1-e i) ≤ (n i:ℝ)-k i+2 := by nlinarith only [pack_i]
    simp only [←Nat.cast_sub kn,←Nat.cast_add_one,←Nat.cast_sub enough] at q
    exact_mod_cast q
  · change (N+P*n i)*m<p i
    exact_mod_cast (show ((N:ℝ)+(P:ℝ)*n i)*m<p i by nlinarith only [size_i])
  · change p i/Q < m*(e i+1)
    exact_mod_cast (show ((p i/Q:ℕ):ℝ) < (m:ℝ)*((e i:ℝ)+1) by nlinarith only [budget_i])

/-- Rounding a fixed relative error down to the Hamming grid preserves its limit. -/
theorem floor_fraction (n : ℕ → ℕ) [∀ i, NeZero (n i)] (hn : Tendsto n atTop atTop)
    {α : ℝ} (ha : 0≤α) :
    Tendsto (fun i => ((⌊α*(n i : ℝ)⌋₊ : ℕ):ℝ)/n i) atTop (𝓝 α) := by
  have l := (tendsto_const_nhds (x:=α)).sub
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  rw [sub_zero] at l
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le l tendsto_const_nhds
  · intro i
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    change α-1/(n i:ℝ) ≤ _
    rw [le_div_iff₀ ni,sub_mul,div_mul_cancel₀ _ ni.ne']
    linarith [Nat.lt_floor_add_one (α*(n i:ℝ))]
  · intro i
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    exact (div_le_iff₀ ni).mpr (Nat.floor_le (mul_nonneg ha ni.le))

/-- A bounded limiting field-size slope is an integer on smooth domains.
Eventually the field size is exactly that integer times the length plus one. -/
theorem coindex_stabilizes (F : ℕ → Type) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [∀ i, DecidableEq (F i)] (n : ℕ → ℕ) [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ F i) [∀ i, ReedSolomon.Smooth (x i)]
    (hn : Tendsto n atTop atTop) {slope : ℝ}
    (hf : Tendsto (fun i => (Fintype.card (F i):ℝ)/n i) atTop (𝓝 slope)) :
    ∃ c : ℕ, (c:ℝ)=slope ∧ ∀ᶠ i in atTop, Fintype.card (F i)=n i*c+1 := by
  classical
  have divides (i : ℕ) : n i ∣ Fintype.card (F i)-1 := by
    obtain ⟨e,_⟩ := SmoothDomainMcaEquivalence.coset_equiv (x i)
    have h := (ReedSolomon.Smooth.H (x i)).card_subgroup_dvd_card
    rw [← Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_fin,Nat.card_units,
      Nat.card_eq_fintype_card] at h
    exact h
  choose d hd using divides
  have factor (i : ℕ) : Fintype.card (F i)=n i*d i+1 := by
    have := Fintype.card_pos (α:=F i)
    obtain h := hd i
    omega
  have sub := hf.sub ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn)
  rw [sub_zero] at sub
  have lim : Tendsto (fun i => (d i:ℝ)) atTop (𝓝 slope) := by
    apply sub.congr
    intro i
    change (Fintype.card (F i):ℝ)/n i-1/n i=(d i:ℝ)
    rw [factor i,Nat.cast_add,Nat.cast_mul,Nat.cast_one,←sub_div,add_sub_cancel_right]
    exact mul_div_cancel_left₀ _ (by exact_mod_cast NeZero.ne (n i))
  have mem : slope ∈ Set.range ((↑) : ℕ → ℝ) :=
    Nat.isClosedEmbedding_coe_real.isClosed_range.mem_of_tendsto lim (.of_forall fun i => ⟨d i,rfl⟩)
  obtain ⟨c,rfl⟩ := mem
  refine ⟨c,rfl,?_⟩
  filter_upwards [lim.eventually_lt_const (show (c:ℝ)<c+1 by linarith),
    lim.eventually_const_lt (show (c:ℝ)-1<c by linarith)] with i h₁ h₂
  have left : c<d i+1 := by exact_mod_cast (show (c:ℝ)<(d i:ℝ)+1 by linarith)
  have right : d i<c+1 := by exact_mod_cast h₁
  simpa [show d i=c by omega] using factor i

/-- A fixed relative-error bound on the threshold itself, without any input
sequence of error counts. The smooth-field coefficient depends only on the
chosen number of heads, independently of block length and field characteristic. -/
theorem eventually_at_most (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) [∀ i, ReedSolomon.Smooth (x i)]
    (d Q : ℕ) (hQ : 0<Q) (hn : Tendsto n atTop atTop) {slope ρ α : ℝ}
    (hf : Tendsto (fun i => (p i : ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i : ℝ)/n i) atTop (𝓝 ρ)) (positive : 0<ρ) (ha : 0≤α)
    (core : ρ+α<1) (pack : ((d+1:ℕ):ℝ)*(1-ρ-α) < 1-ρ)
    (fieldSize : (((edges (d+2)).offDiag.card*(d+1) : ℕ):ℝ) < slope)
    (overBudget : slope/Q < ((d+1:ℕ):ℝ)*α) :
    ∀ᶠ i in atTop, (mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) : ℝ) ≤ α := by
  have bad := eventually_ceiling p n k _ x d Q hQ hn hf rate positive
    (floor_fraction n hn ha) core pack fieldSize overBudget
  filter_upwards [bad] with i hi
  have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
  have upper := (div_le_iff₀ ni).mpr (Nat.floor_le (mul_nonneg ha ni.le))
  exact le_trans (by exact_mod_cast hi) upper

end ProximityGap.SmoothLinearFieldEnvelope
#print axioms ProximityGap.SmoothLinearFieldEnvelope.eventually_ceiling
#print axioms ProximityGap.SmoothLinearFieldEnvelope.eventually_at_most
#print axioms ProximityGap.SmoothLinearFieldEnvelope.coindex_stabilizes
