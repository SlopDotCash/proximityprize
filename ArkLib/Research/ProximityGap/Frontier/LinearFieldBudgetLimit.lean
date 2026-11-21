/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.LinearFieldBudgetRadius

/-! # Linear field growth below the unique-decoding radius -/
set_option autoImplicit false
namespace ProximityGap.LinearFieldBudgetLimit
open Filter Topology LinearFieldBudgetRadius MCAThresholdLedger
open scoped NNReal ENNReal

/-- Rounding the field-size budget costs less than one Hamming step. -/
theorem floor_limit (p n : ℕ → ℕ) (Q : ℕ) (hQ : 0<Q) [∀ i, NeZero (n i)]
    (hn : Tendsto n atTop atTop) {slope : ℝ}
    (hp : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope)) :
    Tendsto (fun i => ((p i/Q:ℕ):ℝ)/n i) atTop (𝓝 (slope/Q)) := by
  have main := hp.div_const (Q:ℝ)
  have zero := (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn
  have low := main.sub zero
  rw [sub_zero] at low
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le low main
  · intro i
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    have qi : (0:ℝ)<Q := by exact_mod_cast hQ
    have up : (p i : ℝ) < (Q:ℝ)*(((p i/Q:ℕ):ℝ)+1) := by exact_mod_cast Nat.lt_mul_div_succ (p i) hQ
    change (p i:ℝ)/n i/Q - 1/(n i:ℝ) ≤ _
    rw [div_right_comm,← sub_div,div_le_div_iff_of_pos_right ni]
    have : (p i:ℝ)/Q < ((p i/Q:ℕ):ℝ)+1 := (div_lt_iff₀ qi).mpr (by linarith)
    linarith
  · intro i
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    have qi : (0:ℝ)<Q := by exact_mod_cast hQ
    have lo : ((p i/Q:ℕ):ℝ)*Q ≤ p i := by exact_mod_cast Nat.div_mul_le_self (p i) Q
    change _ ≤ (p i:ℝ)/n i/Q
    rw [div_right_comm,div_le_div_iff_of_pos_right ni,le_div_iff₀ qi]
    exact lo

/-- For any prescribed prime-field domains, if p/n tends to λ and λ/Q is
strictly below half the relative minimum-distance limit, eventually the
exact radius is floor(p/Q)/n, and its limit is λ/Q. -/
theorem eventually_exact (p n k : ℕ → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (n i)]
    (x : ∀ i, Fin (n i) ↪ ZMod (p i)) (Q : ℕ) (hQ : 0<Q) (hk : ∀ᶠ i in atTop, 1≤k i)
    (hn : Tendsto n atTop atTop) {slope ρ : ℝ}
    (hf : Tendsto (fun i => (p i:ℝ)/n i) atTop (𝓝 slope))
    (rate : Tendsto (fun i => (k i:ℝ)/n i) atTop (𝓝 ρ))
    (slack : ρ+2*(slope/Q)<1) :
    (∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) =
        ((p i/Q:ℕ):ℝ≥0)/n i) ∧
    Tendsto (fun i => (mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) : ℝ))
        atTop (𝓝 (slope/Q)) := by
  let B (i : ℕ) := p i/Q
  let c := (1-(ρ+2*(slope/Q)))/2
  have hc : 0<c := by dsimp [c]; linarith
  have lim := floor_limit p n Q hQ hn hf
  have sumLim := rate.add ((tendsto_const_nhds (x:=(2:ℝ))).mul lim)
  have close := sumLim.eventually_lt_const (show ρ+2*(slope/Q)<1-c by dsimp [c]; linarith)
  let M := ⌈1/c⌉₊+1
  have largeB : ∀ᶠ i in atTop, M≤B i := by
    filter_upwards [hn.eventually_ge_atTop (M*Q)] with i hi
    have bound : n i ≤ p i := by simpa using Fintype.card_le_of_injective _ (x i).injective
    exact (Nat.le_div_iff_mul_le hQ).mpr (hi.trans bound)
  have exact_at : ∀ᶠ i in atTop, mcaDeltaStar (F:=ZMod (p i))
      (ReedSolomon.code (x i) (k i) : Set (Fin (n i) → ZMod (p i))) (1/(Q:ℝ≥0∞)) =
        ((B i:ℕ):ℝ≥0)/n i := by
    filter_upwards [close,largeB,hk] with i hold hb hk
    have ni : (0:ℝ)<n i := by exact_mod_cast NeZero.pos (n i)
    have bpos : 1≤B i := by dsimp [M] at hb; omega
    have big : 1<(B i:ℝ)*c := by
      apply (div_lt_iff₀ hc).mp
      have le := Nat.le_ceil (1/c)
      have gt : ⌈1/c⌉₊ < B i := by dsimp [M] at hb;omega
      exact le.trans_lt (by exact_mod_cast gt)
    change (k i:ℝ)/n i + 2*((B i:ℝ)/n i) < 1-c at hold
    rw [← mul_div_assoc,← add_div] at hold
    have d := (div_lt_iff₀ ni).mp hold
    have realroom : (k i:ℝ)+2*(B i:ℝ) < n i := by nlinarith [mul_pos hc ni]
    have room : k i+2*B i < n i := by exact_mod_cast realroom
    have rem : (c*(n i:ℝ)) ≤ (((n i-k i-2*B i:ℕ)):ℝ) := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_mul,Nat.cast_ofNat]
      linarith
    have strict : (n i:ℝ) < (B i:ℝ)*((n i-k i-2*B i:ℕ):ℝ) := by
      calc (n i:ℝ) < ((B i:ℝ)*c)*n i := by simpa using mul_lt_mul_of_pos_right big ni
           _ = (B i:ℝ)*(c*(n i:ℝ)) := mul_assoc ..
           _ ≤ _ := mul_le_mul_of_nonneg_left rem (Nat.cast_nonneg _)
    have natStrict : n i < B i*(n i-k i-2*B i) := by exact_mod_cast strict
    exact exact_radius (x i) hQ hk (by simp [B]) bpos room.le
      (natStrict.trans_le (Nat.mul_le_mul_left _ (by omega)))
  refine ⟨exact_at,lim.congr' ?_⟩
  filter_upwards [exact_at] with i hi
  rw [hi]
  rfl

end ProximityGap.LinearFieldBudgetLimit
#print axioms ProximityGap.LinearFieldBudgetLimit.eventually_exact
